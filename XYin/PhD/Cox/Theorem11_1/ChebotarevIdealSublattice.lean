/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealCells
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Ideal sublattices and residue classes
Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`.
-/
noncomputable section
open NumberField Set Submodule
open NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace
open scoped NNReal nonZeroDivisors Pointwise
namespace Cox.Chebotarev

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2138. -/
theorem absNorm_coprime_of_isCoprime_span {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (n : ℕ)
    (hcop : IsCoprime (J : Ideal (𝓞 K)) (Ideal.span {(n : 𝓞 K)})) :
    (Ideal.absNorm (J : Ideal (𝓞 K))).Coprime n := by
  by_contra hnc
  obtain ⟨p, hp, hpJ, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp (J : Ideal (𝓞 K)) hpJ
  have hJP : (J : Ideal (𝓞 K)) ≤ P := Ideal.le_of_dvd hPdvd
  have hpP : (p : 𝓞 K) ∈ P := by
    have hpZ : (p : ℤ) ∈ Ideal.under ℤ P := by
      rw [hPunder]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap] at hpZ
    simpa using hpZ
  have hnP : (n : 𝓞 K) ∈ P := by
    obtain ⟨k, hk⟩ := hpn
    rw [hk]
    push_cast
    exact Ideal.mul_mem_right _ _ hpP
  have hspanP : Ideal.span {(n : 𝓞 K)} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hnP
  have hsupP : (J : Ideal (𝓞 K)) ⊔ Ideal.span {(n : 𝓞 K)} ≤ P := sup_le hJP hspanP
  rw [Ideal.isCoprime_iff_sup_eq.mp hcop, top_le_iff] at hsupP
  exact hPmax.ne_top hsupP

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2178. -/
theorem span_image_basisFun_eq {ι : Type*} [Finite ι] (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
    (span ℤ (⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ ι)))) : Submodule ℤ (ι → ℝ))
      = span ℤ (Set.range ((Pi.basisFun ℝ ι).map T)) := by
  have h1 : (⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ ι))) : Set (ι → ℝ))
      = ↑(span ℤ (⇑T '' Set.range (Pi.basisFun ℝ ι)) : Submodule ℤ (ι → ℝ)) :=
    map_span_int_linearEquiv T (Set.range (Pi.basisFun ℝ ι))
  rw [h1, span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  congr 1
  rw [Module.Basis.coe_map, Set.range_comp]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2193. -/
theorem covolume_image_basisFun_eq_abs_det {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
    ZLattice.covolume (span ℤ (Set.range ((Pi.basisFun ℝ ι).map T)) : Submodule ℤ (ι → ℝ))
      = |LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| := by
  classical
  have hli : LinearIndependent ℤ ⇑((Pi.basisFun ℝ ι).map T) :=
    ((Pi.basisFun ℝ ι).map T).linearIndependent.restrict_scalars (by
      simpa using (algebraMap ℤ ℝ).injective_int)
  set b : Module.Basis ι ℤ (span ℤ (Set.range ((Pi.basisFun ℝ ι).map T)) : Submodule ℤ (ι → ℝ)) :=
    Module.Basis.span hli with hbdef
  rw [ZLattice.covolume_eq_det _ b, show ((↑) ∘ b) = ⇑((Pi.basisFun ℝ ι).map T) from
      funext fun i ↦ by rw [Function.comp_apply, hbdef, Module.Basis.coe_span_apply],
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ ι) (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)),
    ← Matrix.det_transpose (LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
      (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))]
  congr 1

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2214. -/
theorem relIndex_mul_ideal_eq_absNorm {K : Type*} [Field K] [NumberField K]
    (J 𝔟 : (Ideal (𝓞 K))⁰) :
    ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup.relIndex
        ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup
      = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
  classical
  have hle : ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup
      ≤ ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le]
    push_cast
    exact Ideal.mul_le_left
  have key := AddSubgroup.relIndex_mul_index hle
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index] at key
  have hNbJ : Ideal.absNorm ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    rw [Submonoid.coe_mul, map_mul]
  rw [hNbJ] at key
  exact Nat.eq_of_mul_eq_mul_right (Ideal.absNorm_pos_of_nonZeroDivisors J) key

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2236. -/
theorem idealLattice_mul_le {K : Type*} [Field K] [NumberField K]
    (J 𝔟 : (Ideal (𝓞 K))⁰) :
    NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K (𝔟 * J))
      ≤ NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) := by
  intro x hx
  rw [NumberField.mixedEmbedding.mem_idealLattice] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  have hsub : (FractionalIdeal.mk0 K (𝔟 * J) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) := by
    simp only [FractionalIdeal.coe_mk0]
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    exact Ideal.mul_le_left
  exact hsub hy

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2255. -/
theorem idealLattice_toAddSubgroup_eq {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    (NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).toAddSubgroup
      = ((J : Ideal (𝓞 K)).toAddSubgroup).map
          (((NumberField.mixedEmbedding K).toAddMonoidHom).comp
            (algebraMap (𝓞 K) K).toAddMonoidHom) := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, NumberField.mixedEmbedding.mem_idealLattice,
    AddSubgroup.mem_map, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [FractionalIdeal.coe_mk0] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨algebraMap (𝓞 K) K z, ?_, rfl⟩
    simp only [FractionalIdeal.coe_mk0]
    exact ⟨z, hz, rfl⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2279. -/
theorem relIndex_idealLattice_eq_absNorm {K : Type*} [Field K] [NumberField K]
    (J 𝔟 : (Ideal (𝓞 K))⁰) :
    (NumberField.mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K (𝔟 * J))).toAddSubgroup.relIndex
        (NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).toAddSubgroup
      = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
  have hinj : Function.Injective
      (((NumberField.mixedEmbedding K).toAddMonoidHom).comp
        (algebraMap (𝓞 K) K).toAddMonoidHom) := by
    rw [AddMonoidHom.coe_comp]
    exact (NumberField.mixedEmbedding_injective K).comp (IsFractionRing.injective (𝓞 K) K)
  rw [idealLattice_toAddSubgroup_eq, idealLattice_toAddSubgroup_eq,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, relIndex_mul_ideal_eq_absNorm]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2296. -/
theorem chart_lattice_eq_map {K : Type*} [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ))) :
    (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) : Submodule ℤ (index K → ℝ))
      = (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).map
          (((mixedEmbedding.stdBasis K).equivFunL :
            mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap := by
  rw [← span_image_basisFun_eq, hT]
  have : ((mixedEmbedding.stdBasis K).equivFunL ''
        ((mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) : Set (mixedSpace K))
        : Set (index K → ℝ))
      = ↑((mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).map
          (((mixedEmbedding.stdBasis K).equivFunL :
            mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap) := by
    rw [Submodule.map_coe]
    rfl
  rw [this, span_coe_eq_restrictScalars, Submodule.restrictScalars_self]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2318. -/
theorem chart_sublattice_le {K : Type*} [Field K] [NumberField K] (J 𝔟 : (Ideal (𝓞 K))⁰)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
    (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T')) : Submodule ℤ (index K → ℝ))
      ≤ span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) := by
  rw [chart_lattice_eq_map J T hT, chart_lattice_eq_map (𝔟 * J) T' hT']
  exact Submodule.map_mono (idealLattice_mul_le J 𝔟)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2334. -/
theorem relIndex_chart_eq_absNorm {K : Type*} [Field K] [NumberField K]
    (J 𝔟 : (Ideal (𝓞 K))⁰)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
    (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))).toAddSubgroup.relIndex
        (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))).toAddSubgroup
      = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
  have hΦinj : Function.Injective
      (((mixedEmbedding.stdBasis K).equivFunL :
        mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap :=
    ((mixedEmbedding.stdBasis K).equivFunL : mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).injective
  rw [chart_lattice_eq_map J T hT, chart_lattice_eq_map (𝔟 * J) T' hT',
    Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hΦinj]
  exact relIndex_idealLattice_eq_absNorm J 𝔟

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2362. -/
theorem abs_det_latticeEquiv_mul {K : Type*} [Field K] [NumberField K]
    (J 𝔟 : (Ideal (𝓞 K))⁰)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
    |LinearMap.det (T' : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
      = (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)
        * |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| := by
  classical
  set L : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))
  set L' : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
  have hcov := ZLattice.covolume_div_covolume_eq_relIndex L' L
    (chart_sublattice_le J 𝔟 T T' hT hT')
  rw [relIndex_chart_eq_absNorm J 𝔟 T T' hT hT',
    covolume_image_basisFun_eq_abs_det, covolume_image_basisFun_eq_abs_det] at hcov
  have hdetJ : (0 : ℝ) < |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| :=
    abs_pos.mpr (LinearEquiv.isUnit_det' T).ne_zero
  field_simp at hcov
  linarith [hcov]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2393. -/
theorem crt_single_coset {ι : Type*} [Finite ι] (L L' : Submodule ℤ (ι → ℝ))
    (hle : L' ≤ L)
    [Finite (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)]
    (m : ℕ)
    (hcop : (Nat.card (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)).Coprime m)
    {ξ : ι → ℝ} (hξ : ξ ∈ L) :
    ∃ ξ' : ι → ℝ, ξ' ∈ L' ∧
      {a : ι → ℝ | a ∈ L' ∧ a ∈ ξ +ᵥ ((m : ℝ) • (L : Set (ι → ℝ)))}
        = (ξ' +ᵥ ((m : ℝ) • (L' : Set (ι → ℝ)))) := by
  have hmsmul : ∀ (M : Submodule ℤ (ι → ℝ)), ((m : ℝ) • (M : Set (ι → ℝ)))
      = {z | ∃ x ∈ M, z = m • x} := by
    intro M
    ext z
    simp only [Set.mem_smul_set, SetLike.mem_coe, Set.mem_setOf_eq]
    exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, by rw [← h, Nat.cast_smul_eq_nsmul]⟩,
      fun ⟨x, hx, h⟩ ↦ ⟨x, hx, by rw [h, Nat.cast_smul_eq_nsmul]⟩⟩
  have hbij := hcop.nsmul_right_bijective
    (G := L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
  have hsurj : ∃ a' ∈ L'.toAddSubgroup, ∃ a ∈ L.toAddSubgroup, ξ = a' + m • a := by
    obtain ⟨q, hq⟩ := hbij.2 (QuotientAddGroup.mk (⟨ξ, hξ⟩ : L.toAddSubgroup))
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only at hq
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
    exact ⟨(-(m • (a : ι → ℝ)) + ξ), by simpa using hq, (a : ι → ℝ), a.2, by abel⟩
  obtain ⟨ξ', hξ'L', a₀, ha₀L, hξeq⟩ := hsurj
  refine ⟨ξ', hξ'L', ?_⟩
  have hinj2 : ∀ a : ι → ℝ, a ∈ L → m • a ∈ L' → a ∈ L' := by
    intro a ha hma
    have hzero : m • (QuotientAddGroup.mk (⟨a, ha⟩ : L.toAddSubgroup)
        : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
        = (0 : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) := by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hma
    have hq0 : (QuotientAddGroup.mk (⟨a, ha⟩ : L.toAddSubgroup)
        : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 :=
      hbij.1 (by simp only [hzero, smul_zero])
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hq0
    simpa using hq0
  ext a
  simp only [Set.mem_setOf_eq, hmsmul, Set.mem_vadd_set, Set.mem_setOf_eq, vadd_eq_add]
  constructor
  · rintro ⟨haL', w, ⟨x, hxL, rfl⟩, hweq⟩
    rw [hξeq] at hweq
    have hmem : m • (a₀ + x) = a - ξ' := by
      rw [smul_add, ← hweq]
      abel
    refine ⟨a - ξ', ⟨a₀ + x, ?_, ?_⟩, by abel⟩
    · exact hinj2 _ (L.add_mem ha₀L hxL) (by rw [hmem]; exact L'.sub_mem haL' hξ'L')
    · rw [hmem]
  · rintro ⟨w, ⟨y, hyL', rfl⟩, rfl⟩
    refine ⟨L'.add_mem hξ'L' (L'.nsmul_mem hyL' m), m • (y - a₀),
      ⟨y - a₀, L.sub_mem (hle hyL') ha₀L, rfl⟩, ?_⟩
    rw [hξeq, smul_sub]
    abel

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2455. -/
theorem exists_mk0_eq_absNorm_coprime {K : Type*} [Field K] [NumberField K]
    (D : ClassGroup (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ∃ J : (Ideal (𝓞 K))⁰, ClassGroup.mk0 J = D ∧
      (Ideal.absNorm (J : Ideal (𝓞 K))).Coprime n := by
  classical
  rcases eq_or_ne n 1 with rfl | hn1
  · obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective D
    exact ⟨J, hJ, Nat.coprime_one_right _⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨J₀, hJ₀⟩ := ClassGroup.mk0_surjective D⁻¹
  have hJ₀ne : (J₀ : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J₀
  set 𝔫 : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)} with h𝔫
  have hnZ : (n : 𝓞 K) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := 𝓞 K)).mpr hn.ne'
  have h𝔫ne : 𝔫 ≠ ⊥ := by
    rwa [h𝔫, Ne, Ideal.span_singleton_eq_bot]
  have h𝔫top : 𝔫 ≠ ⊤ := by
    rw [Ne, ← Ideal.absNorm_eq_one_iff, h𝔫, Ideal.absNorm_span_natCast]
    have : 2 ≤ n ^ Module.finrank ℤ (𝓞 K) :=
      le_trans hn2 (Nat.le_self_pow Module.finrank_pos.ne' n)
    omega
  have hle : 𝔫 * (J₀ : Ideal (𝓞 K)) ≤ (J₀ : Ideal (𝓞 K)) := Ideal.mul_le_left
  have hIne : 𝔫 * (J₀ : Ideal (𝓞 K)) ≠ 0 := mul_ne_zero h𝔫ne hJ₀ne
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hIne
  have hane : a ≠ 0 := by
    intro hbot
    rw [hbot, Ideal.span_singleton_zero, sup_bot_eq] at ha
    apply h𝔫top
    have : (J₀ : Ideal (𝓞 K)) * 𝔫 = (J₀ : Ideal (𝓞 K)) * ⊤ := by
      rwa [Ideal.mul_top, mul_comm]
    exact mul_left_cancel₀ hJ₀ne this
  have haJ₀ : Ideal.span {a} ≤ (J₀ : Ideal (𝓞 K)) := le_sup_right.trans (le_of_eq ha)
  obtain ⟨J₁, hJ₁⟩ : (J₀ : Ideal (𝓞 K)) ∣ Ideal.span {a} := Ideal.dvd_iff_le.mpr haJ₀
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ₁
    exact hane hJ₁
  have hcop : 𝔫 ⊔ J₁ = ⊤ := by
    have hkey : (J₀ : Ideal (𝓞 K)) * (𝔫 ⊔ J₁) = (J₀ : Ideal (𝓞 K)) * ⊤ := by
      calc (J₀ : Ideal (𝓞 K)) * (𝔫 ⊔ J₁)
          = (J₀ : Ideal (𝓞 K)) * 𝔫 ⊔ (J₀ : Ideal (𝓞 K)) * J₁ := Ideal.mul_sup _ _ _
        _ = 𝔫 * (J₀ : Ideal (𝓞 K)) ⊔ Ideal.span {a} := by rw [mul_comm (J₀ : Ideal (𝓞 K)) 𝔫, hJ₁]
        _ = (J₀ : Ideal (𝓞 K)) := ha
        _ = (J₀ : Ideal (𝓞 K)) * ⊤ := (Ideal.mul_top _).symm
    exact mul_left_cancel₀ hJ₀ne hkey
  have hJ₁mem : J₁ ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hJ₁ne
  have hsaZ : Ideal.span {a} ≠ 0 := by
    rwa [Submodule.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
  set J₁' : (Ideal (𝓞 K))⁰ := ⟨J₁, hJ₁mem⟩ with hJ₁'
  refine ⟨J₁', ?_, ?_⟩
  · have hsa_mem : Ideal.span {a} ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hsaZ
    have hprinc : ClassGroup.mk0 (⟨Ideal.span {a}, hsa_mem⟩ : (Ideal (𝓞 K))⁰) = 1 :=
      (ClassGroup.mk0_eq_one_iff hsa_mem).mpr ⟨a, rfl⟩
    have hfact : (⟨Ideal.span {a}, hsa_mem⟩ : (Ideal (𝓞 K))⁰) = J₀ * J₁' :=
      Subtype.ext (by simp only [Submonoid.coe_mul, hJ₁', hJ₁])
    rw [hfact, map_mul, hJ₀] at hprinc
    have hinv := mul_eq_one_iff_eq_inv.mp hprinc
    rw [← inv_inv (ClassGroup.mk0 J₁'), ← hinv, inv_inv]
  · have hcopI : IsCoprime (J₁ : Ideal (𝓞 K)) 𝔫 := by
      rwa [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact absNorm_coprime_of_isCoprime_span J₁' n (by
      simpa only [hJ₁'] using hcopI)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2518. -/
theorem image_range_basisFun_eq {ι : Type*} [Finite ι] (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
    (⇑T '' Set.range (Pi.basisFun ℝ ι)) = Set.range ((Pi.basisFun ℝ ι).map T) := by
  rw [Module.Basis.coe_map, Set.range_comp]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2525. -/
theorem smul_chart_lattice_eq {ι : Type*} [Finite ι] (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (m : ℕ) (hm : (m : ℝ) ≠ 0) :
    (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T) ''
      (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))
      = ((m : ℝ) • (span ℤ (Set.range ((Pi.basisFun ℝ ι).map T)) : Set (ι → ℝ))) := by
  have hLeq : (span ℤ (Set.range ((Pi.basisFun ℝ ι).map T)) : Set (ι → ℝ))
      = ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    rw [map_span_int_linearEquiv, image_range_basisFun_eq]
  ext z
  simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, Set.mem_image,
    Set.mem_smul_set, SetLike.mem_coe, hLeq]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨T v, ⟨v, hv, rfl⟩, by rw [map_smul]⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, by rw [map_smul]⟩

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2547. -/
theorem exists_card_fibre_dvd_eq_card_cell {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (hcop : (Ideal.absNorm (𝔟 : Ideal (𝓞 K))).Coprime m)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)))
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
    {t : ℝ} (ht : 1 ≤ t) :
    ∃ ξ' : index K → ℝ, Nat.card {a : idealSet K (𝔟 * J) //
        mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = k}
      = Nat.card ↑((ξ' +ᵥ ((m : ℝ) • (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
          : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  set L : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))
    with hLdef
  set L' : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
    with hL'def
  have hrel : L'.toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) :=
    relIndex_chart_eq_absNorm J 𝔟 T T' hT hT'
  have hNB : 0 < Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  haveI hfin : Finite (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) := by
    rw [← AddSubgroup.index_ne_zero_iff_finite]
    rw [show (L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup).index
        = L'.toAddSubgroup.relIndex L.toAddSubgroup from rfl, hrel]
    exact hNB.ne'
  have hcopC : (Nat.card (L.toAddSubgroup ⧸
      L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)).Coprime m := by
    rw [show Nat.card (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
        = L'.toAddSubgroup.relIndex L.toAddSubgroup from rfl, hrel]
    exact hcop
  have hLL' : L' ≤ L := chart_sublattice_le J 𝔟 T T' hT hT'
  have hξkL : (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) ∈ L := by
    have hv : (fun i ↦ ((k i).val : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) := by
      rw [mem_span_int_basisFun_iff]
      exact fun i ↦ ⟨((k i).val : ℤ), by push_cast; rfl⟩
    have hmem : (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ)
        ∈ ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := ⟨_, hv, rfl⟩
    rw [map_span_int_linearEquiv] at hmem
    rw [hLdef]
    rwa [image_range_basisFun_eq] at hmem
  obtain ⟨ξ', hξ'L', hcoset⟩ := crt_single_coset L L' hLL' m hcopC hξkL
  refine ⟨ξ', ?_⟩
  have hΦΛ' : ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) = ↑L' := by
    rw [hL'def, ← hT', map_span_int_linearEquiv, image_range_basisFun_eq]
  have hincl : idealSet K (𝔟 * J) ⊆ idealSet K J := by
    intro x hx
    exact ⟨hx.1, idealLattice_mul_le J 𝔟 hx.2⟩
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  have hreg : ∀ x : mixedSpace K, x ∈ idealSet K J →
      (Φ x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os) ↔
        (mixedEmbedding.norm x ≤ t ^ d ∧
          Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s)) :=
    fun x hx ↦ mem_smul_cell_iff_norm_le_and_filter_eq J s ht hx
  set f : {a : idealSet K (𝔟 * J) //
      mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} → (index K → ℝ) :=
    fun a ↦ Φ (a.1 : mixedSpace K) with hf
  have hfinj : Function.Injective f := fun _ _ h ↦ Subtype.ext (Subtype.ext (Φ.injective h))
  have hset : Set.range f =
      ((ξ' +ᵥ ((m : ℝ) • (L' : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) := by
    ext y
    simp only [hf, Set.mem_range, Subtype.exists, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hP, rfl⟩
      have haJ : a ∈ idealSet K J := hincl ha
      have haL' : Φ a ∈ L' := by
        have hmm : Φ a ∈ ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) := ⟨a, ha.2, rfl⟩
        rwa [hΦΛ'] at hmm
      have hcosetmem : Φ a ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) :=
        (mem_coset_iff_cos_eq m hm J T hT k haJ.2).mpr (fun i ↦ congrFun hP.2.2 i)
      have hΦacoset : Φ a ∈ ξ' +ᵥ ((m : ℝ) • (L' : Set (index K → ℝ))) := by
        have hmemL : Φ a ∈ {b | b ∈ L' ∧ b ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
            ((m : ℝ) • (L : Set (index K → ℝ)))} := by
          refine ⟨haL', ?_⟩
          rw [hLdef, ← smul_chart_lattice_eq T m hm]
          exact hcosetmem
        rwa [hcoset] at hmemL
      exact ⟨hΦacoset, (hreg a haJ).mpr ⟨hP.1, hP.2.1⟩⟩
    · rintro ⟨hcosetmem, hregion⟩
      have hyL' : y ∈ L' := by rw [hcoset.symm] at hcosetmem; exact hcosetmem.1
      have hyΛ' : y ∈ ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) := by rw [hΦΛ']; exact hyL'
      obtain ⟨z, hzlat, hzeq⟩ := hyΛ'
      have hzcone : z ∈ idealSet K (𝔟 * J) :=
        mem_idealSet_of_chart_mem_smul_cell (𝔟 * J) ht0 hzlat hzeq hregion
      have hzJ : z ∈ idealSet K J := hincl hzcone
      have hcosetz : Φ z ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) := by
        have hymem : y ∈ {a | a ∈ L' ∧ a ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
            ((m : ℝ) • (L : Set (index K → ℝ)))} := by rw [hcoset]; exact hcosetmem
        rw [smul_chart_lattice_eq T m hm, ← hLdef, show (Φ z : index K → ℝ) = y from hzeq]
        exact hymem.2
      refine ⟨z, hzcone, ⟨?_, ?_, ?_⟩, hzeq⟩
      · exact ((hreg z hzJ).mp (by rw [hzeq]; exact hregion)).1
      · exact ((hreg z hzJ).mp (by rw [hzeq]; exact hregion)).2
      · funext i
        exact (mem_coset_iff_cos_eq m hm J T hT k hzJ.2).mp hcosetz i
  rw [← Nat.card_range_of_injective hfinj, hset]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2692. -/
theorem abs_det_smulTrans_mul {K : Type*} [Field K] [NumberField K]
    (m : ℝ) (hm : m ≠ 0) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
    |LinearMap.det ((((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) m hm).trans T'
        : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ)))|
      = (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)
        * |LinearMap.det ((((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) m hm).trans T
            : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ)))| := by
  have hdet := abs_det_latticeEquiv_mul J 𝔟 T T' hT hT'
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.det_comp, LinearMap.det_comp,
    abs_mul, abs_mul, hdet]
  ring

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2721. -/
theorem exists_card_fibre_dvd_residue_sub_mul_rpow_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (hcop : (Ideal.absNorm (𝔟 : Ideal (𝓞 K))).Coprime m)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K (𝔟 * J) //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ)
          - ((if (∃ a : idealSet K J,
              (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
                (a : mixedSpace K).1 w < 0) = s) ∧
              ((fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
                (a : mixedSpace K))) i) : ZMod m)) = k) ∧
              ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
            then MeasureTheory.volume.real
              ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
                {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})
              / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
                : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
            else 0) / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)) * t ^ Module.finrank ℚ K|
        ≤ C * t ^ (Module.finrank ℚ K - 1 : ℕ) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hcard : Fintype.card (index K) = d := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  obtain ⟨cellC', hcell'⟩ := exists_card_cell_sub_mul_rpow_le_explicit T' m hm
    (Φ '' (normLeOne K)) (Φ.lipschitz.isBounded_image (isBounded_normLeOne K))
    ((Φ.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (measurableSet_normLeOne K))
    hcov (Sum.inl : {w : InfinitePlace K // IsReal w} → index K) s
  have hdetratio : MeasureTheory.volume.real (Φ '' (normLeOne K) ∩ Os)
        / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T'
          : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
      = MeasureTheory.volume.real (Φ '' (normLeOne K) ∩ Os)
          / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
            : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| / NB := by
    rw [abs_det_smulTrans_mul m hm J 𝔟 T T' hT hT', ← hNBdef, div_div, mul_comm (NB : ℝ), ← div_div]
  refine ⟨|cellC'|, fun t ht ↦ ?_⟩
  by_cases hQ : ∃ a : idealSet K J,
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      ((fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k) ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))
  · obtain ⟨a₀, horth₀, hcos₀, hres₀⟩ := hQ
    rw [if_pos ⟨a₀, horth₀, hcos₀, hres₀⟩]
    have hdrop : Nat.card {a : idealSet K (𝔟 * J) //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k}
        = Nat.card {a : idealSet K (𝔟 * J) //
          mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
      constructor
      · rintro ⟨⟨hn, _⟩, ho, hc⟩; exact ⟨hn, ho, hc⟩
      · rintro ⟨hn, ho, hc⟩
        refine ⟨⟨hn, ?_⟩, ho, hc⟩
        have haJ : (a : mixedSpace K) ∈ idealSet K J :=
          ⟨a.2.1, idealLattice_mul_le J 𝔟 a.2.2⟩
        have hkey := residue_fibre_const_aux m b J T hT s k ⟨(a : mixedSpace K), haJ⟩ a₀ ho hc
          horth₀ hcos₀
        exact hkey.mpr hres₀
    obtain ⟨ξ', hξ'⟩ := exists_card_fibre_dvd_eq_card_cell m hm J 𝔟 hcop T T' hT hT' s k ht
    rw [hdrop, hξ']
    have hcell'' := hcell' ξ' t ht
    rw [smul_chart_lattice_eq T' m hm, ← hOs, hdetratio, hcard] at hcell''
    exact hcell''.trans (by gcongr; exact le_abs_self _)
  · rw [if_neg hQ, zero_div, zero_mul, sub_zero]
    have : IsEmpty {a : idealSet K (𝔟 * J) //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine ⟨fun a ↦ hQ ⟨⟨(a.1 : mixedSpace K), a.1.2.1, idealLattice_mul_le J 𝔟 a.1.2.2⟩,
        a.2.2.1, a.2.2.2, ?_⟩⟩
      exact a.2.1.2
    rw [Nat.card_of_isEmpty, Nat.cast_zero, abs_zero]
    positivity

end Cox.Chebotarev
