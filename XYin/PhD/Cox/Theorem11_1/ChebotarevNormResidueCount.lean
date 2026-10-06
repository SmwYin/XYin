/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs
import XYin.PhD.Cox.Theorem11_1.ChebotarevCharacters
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealSublattice
import XYin.PhD.Cox.Theorem11_1.ChebotarevNormBoundary
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Effective counts by norm residue

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`,
ForMathlib/IdealCongruenceCount.lean. Source-local geometric prerequisites precede this module.
-/
noncomputable section
open NumberField Filter Topology Set nonZeroDivisors Submodule
open NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace
open scoped NNReal
namespace Cox.Chebotarev

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:524; norm-residue child. -/
theorem card_norm_le_residue_eq_sum_class {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (a : ZMod c) (N : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}
    = ∑ C : ClassGroup (𝓞 K),
        Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := by
  classical
  have hbase : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
    Ideal.finite_setOf_absNorm_le₀ N
  have hfin : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} :=
    Finite.of_injective (fun I ↦ (⟨I.1, I.2.1⟩ :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
      (fun x y h ↦ Subtype.ext (by simpa using h))
  have hfinC : ∀ C : ClassGroup (𝓞 K), Finite {I : (Ideal (𝓞 K))⁰ //
      (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := fun C ↦
    Finite.of_injective (fun I ↦ (⟨I.1, I.2.1.1⟩ :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
      (fun x y h ↦ Subtype.ext (by simpa using h))
  have hF : Fintype {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} := Fintype.ofFinite _
  have hFC : ∀ C, Fintype {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} :=
    fun C ↦ Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Finset.sum_congr rfl (fun C _ ↦ Nat.card_eq_fintype_card (α := {I : (Ideal (𝓞 K))⁰ //
      (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C})),
    ← Fintype.card_sigma]
  refine Fintype.card_congr ((Equiv.sigmaFiberEquiv (fun I :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} ↦ ClassGroup.mk0 I.1)).symm.trans ?_)
  refine Equiv.sigmaCongrRight (fun C ↦ ?_)
  exact {
    toFun := fun I ↦ ⟨I.1.1, I.1.2, I.2⟩
    invFun := fun I ↦ ⟨⟨I.1, I.2.1⟩, I.2.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:568; norm-residue child. -/
theorem natCast_eq_iff_mul_natCast_eq (cc NJ m a : ℕ) (hNJ : 0 < NJ) :
    ((m : ZMod cc) = (a : ZMod cc)) ↔
      (((m * NJ : ℕ) : ZMod (cc * NJ)) = ((a * NJ : ℕ) : ZMod (cc * NJ))) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.ModEq,
    Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
  exact ⟨fun h ↦ by rw [h], fun h ↦ Nat.eq_of_mul_eq_mul_right hNJ h⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:581; norm-residue child. -/
theorem principalize_iff {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (a : ZMod c) (N : ℕ) (C : ClassGroup (𝓞 K)) (J I : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
    ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C) ↔
      (IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∧
        Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
          N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))))) := by
  classical
  have hnorm : Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]; ring
  have hprin : IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ↔
      ClassGroup.mk0 I = C := by
    have hmem : (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
      SetLike.coe_mem _
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have hmk : ClassGroup.mk0 (⟨(((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), hmem⟩ :
        (Ideal (𝓞 K))⁰) = ClassGroup.mk0 ((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) := by congr 1
    rw [hmk, Equiv.dvd_apply, map_mul, hJ, inv_mul_eq_one, eq_comm]
  rw [hprin, hnorm]
  have hres : (((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ↔
      (((Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
          ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
        ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
          ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))) := by
    rw [show ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a ↔
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((a.val : ℕ) : ZMod c) by
      rw [ZMod.natCast_val, ZMod.cast_id]]
    exact natCast_eq_iff_mul_natCast_eq c (Ideal.absNorm (J : Ideal (𝓞 K)))
      (Ideal.absNorm (I : Ideal (𝓞 K))) a.val hNJ
  have hnle : (Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) ≤
      N * Ideal.absNorm (J : Ideal (𝓞 K))) ↔ (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N) :=
    Nat.mul_le_mul_right_iff hNJ
  rw [hnle, ← hres]
  tauto

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:627; norm-residue child. -/
theorem card_principalize {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (a : ZMod c) (N : ℕ) (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C}
    = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
        (IsPrincipal (I : Ideal (𝓞 K)) ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
  classical
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  exact Nat.card_congr
    (((Equiv.dvd J).subtypeEquiv (fun I ↦ principalize_iff c a N C J I hJ hNJ)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _))

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:901; norm-residue child. -/
theorem card_isPrincipal_dvd_norm_le_residue {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m b : ℕ) (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
        (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} * torsionOrder K =
        Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} := by
  obtain hs | hs := le_or_gt 0 s
  · rw [torsionOrder, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
    refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I ↦ ⟨Ideal.absNorm I.1.val.1, Finset.mem_Iic.mpr (Nat.le_floor I.1.prop.2.2.1)⟩)
      (fun a ↦ ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr
        (Nat.le_floor (by rw [intNorm_idealSetEquiv_apply]; exact a.prop.1))⟩) fun ⟨i, hi⟩ ↦ ?_
    simp_rw [Subtype.mk.injEq]
    have hile : (i : ℝ) ≤ s := (Nat.le_floor_iff hs).mp (Finset.mem_Iic.mp hi)
    by_cases hib : (i : ZMod m) = (b : ZMod m)
    · calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} //
                Ideal.absNorm I.1.1 = i} × torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
          _ ≃ {I : (Ideal (𝓞 K))⁰ // ((J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))) ∧
                Ideal.absNorm I.1 = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeSubtypeEquivSubtypeInter
                (p := fun I : (Ideal (𝓞 K))⁰ ↦ (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                  (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                  ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))
                (q := fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K)) = i)
          _ ≃ {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun I ↦ by
                constructor
                · rintro ⟨⟨h1, h2, _, _⟩, h5⟩; exact ⟨h1, h2, h5⟩
                · rintro ⟨h1, h2, h3⟩
                  exact ⟨⟨h1, h2, by rw [h3]; exact hile, by rw [h3]; exact hib⟩, h3⟩
          _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
                (idealSetEquivNorm K J i).symm
          _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
                simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]; rfl
          _ ≃ _ := (Equiv.subtypeSubtypeEquivSubtype (p := fun a : idealSet K J ↦
                mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
                  ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
                (q := fun a ↦ intNorm (idealSetEquiv K J a).1 = i) fun {a} h ↦ by
                beta_reduce at h ⊢
                rw [← intNorm_idealSetEquiv_apply, h]
                exact ⟨by exact_mod_cast hile, by rw [h] at *; exact hib⟩).symm
    · have : IsEmpty {a : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} //
          intNorm (idealSetEquiv K J a.1).1 = i} := ⟨fun a ↦ hib (by rw [← a.2]; exact a.1.2.2)⟩
      have : IsEmpty {a : ({I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
          (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} × torsion K) //
          Ideal.absNorm a.1.1.1 = i} := ⟨fun a ↦ hib (by rw [← a.2]; exact a.1.1.2.2.2.2)⟩
      exact Equiv.equivOfIsEmpty _ _
  · have : IsEmpty {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
        (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} :=
      ⟨fun I ↦ absurd I.2.2.2.1 (not_le.mpr (lt_of_lt_of_le hs (Nat.cast_nonneg _)))⟩
    have : IsEmpty {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} :=
      ⟨fun a ↦ absurd a.2.1 (not_le.mpr (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)))⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty, zero_mul]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1742; norm-residue child. -/
theorem exists_card_idealSet_residue_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (b : ℕ) (J : (Ideal (𝓞 K))⁰) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
            ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  set NJ := Ideal.absNorm (J : Ideal (𝓞 K)) with hNJdef
  have hNJ : 0 < NJ := Ideal.absNorm_pos_of_nonZeroDivisors J
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  obtain ⟨T, hT⟩ := exists_latticeEquiv_image_idealLattice J
  obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K
  have hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
      (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier (Φ '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := ⟨mc, M, φ, hφ, hcovraw⟩
  choose L C hLC using fun p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) ↦
    exists_card_residue_fibre_sub_mul_rpow_le m hm b J T hT hcov p.1 p.2
  refine ⟨(∑ p, L p) * NJ, (∑ p, |C p|) * (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹), fun N hN ↦ ?_⟩
  have hNN1 : 1 ≤ ((N * NJ : ℕ) : ℝ) := by
    rw [Nat.one_le_cast]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hN) hNJ.ne')
  have hbase := card_residue_sum_bound_aux m b J T ((N * NJ : ℕ) : ℝ) hNN1 L (fun p ↦ |C p|)
    (fun p tN htN ↦ (hLC p tN htN).trans (by gcongr; exact le_abs_self _))
  rw [show (∑ p, L p) * NJ * (N : ℝ) = (∑ p, L p) * ((N * NJ : ℕ) : ℝ) by push_cast; ring]
  refine hbase.trans (le_of_eq ?_)
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg NJ),
    mul_comm ((N : ℝ) ^ _) ((NJ : ℝ) ^ _), ← mul_assoc]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1785; norm-residue child. -/
theorem exists_card_dvd_principal_residue_eq_sub_mul_rpow_le
    {K : Type*} [Field K] [NumberField K] (m : ℕ) [NeZero m] (b : ℕ) (J : (Ideal (𝓞 K))⁰) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
            (IsPrincipal (I : Ideal (𝓞 K)) ∧
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨κ, C', hcore⟩ := exists_card_idealSet_residue_le m b J
  have htors : (0 : ℝ) < torsionOrder K :=
    mod_cast (torsionOrder K).pos_of_ne_zero (torsionOrder_ne_zero K)
  refine ⟨κ / torsionOrder K, C' / torsionOrder K, fun N hN ↦ ?_⟩
  set cnt : ℝ := (Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
    (IsPrincipal (I : Ideal (𝓞 K)) ∧
    Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) with hcnt
  set cone : ℝ := (Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
    ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
    ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) with hcone
  have hcount : cnt * torsionOrder K = cone := by
    rw [hcnt, hcone, ← Nat.cast_mul]
    congr 1
    rw [← card_isPrincipal_dvd_norm_le_residue J m b
      ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ)]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ by simp only [Nat.cast_le])
  have he : |cnt - κ / torsionOrder K * N| = |cone - κ * N| / torsionOrder K := by
    rw [eq_div_iff htors.ne', ← hcount,
      show cnt * torsionOrder K - κ * N
        = torsionOrder K * (cnt - κ / torsionOrder K * N) by field_simp,
      abs_mul, abs_of_pos htors, mul_comm]
  rw [he, div_le_iff₀ htors]
  calc |cone - κ * N| ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := hcore N hN
    _ = C' / torsionOrder K * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) * torsionOrder K := by
        field_simp

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1831; norm-residue child. -/
theorem exists_card_norm_le_residue_class_eq_sub_mul_rpow_le
    {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) (C : ClassGroup (𝓞 K)) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) := Ideal.absNorm_pos_of_nonZeroDivisors J
  haveI : NeZero (c * Ideal.absNorm (J : Ideal (𝓞 K))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne c) hNJ.ne'⟩
  obtain ⟨κ, C', hκ⟩ := exists_card_dvd_principal_residue_eq_sub_mul_rpow_le
    (c * Ideal.absNorm (J : Ideal (𝓞 K))) (a.val * Ideal.absNorm (J : Ideal (𝓞 K))) J
  refine ⟨κ, C', fun N hN ↦ ?_⟩
  rw [card_principalize c a N C J hJ hNJ]
  exact hκ N hN

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1855; norm-residue child. -/
theorem tendsto_div_atTop_of_sub_mul_rpow_le {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ}
    (hd : 0 < d) (hbound : ∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) :
    Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  have hzero : Filter.Tendsto (fun N : ℕ ↦ |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      by
    have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hdpos
    have h2 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    simpa using h2.const_mul |C'|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
    mul_comm (N : ℝ) κ]
  refine (hbound N hN).trans ?_
  have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
    rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
  rw [hsplit, ← mul_assoc]
  gcongr
  exact le_abs_self C'

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1887; norm-residue child. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  choose κf C'f hκf using fun C : ClassGroup (𝓞 K) ↦
    exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c a C
  refine ⟨∑ C : ClassGroup (𝓞 K), κf C, ∑ C : ClassGroup (𝓞 K), |C'f C|, fun N hN ↦ ?_⟩
  rw [card_norm_le_residue_eq_sum_class c a N, Nat.cast_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun C _ ↦ ?_
  exact (hκf C N hN).trans (by gcongr; exact le_abs_self _)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1909; norm-residue child. -/
def cardNormLeResidue (K : Type*) [Field K] [NumberField K] (c : ℕ) (a : ZMod c)
    (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1916; norm-residue child. -/
theorem exists_tendsto_cardNormLeResidue_div (K : Type*) [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ : ℝ, Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c a N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by
  obtain ⟨κ, C', hκ⟩ := exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c a
  exact ⟨κ, tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos hκ⟩

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1929; norm-residue child. -/
theorem cardNormLeResidue_density_eq_of_mem_subgroup {K : Type*} [Field K] [NumberField K]
    {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (cardNormLeResidue K c ((s : (ZMod c)ˣ) : ZMod c) N : ℂ)) / (N : ℂ))
        Filter.atTop (nhds 0))
    {a a' : (ZMod c)ˣ} (ha : a ∈ S) (ha' : a' ∈ S) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a' : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  choose κf hκf using fun s : S ↦
    exists_tendsto_cardNormLeResidue_div K c ((s : (ZMod c)ˣ) : ZMod c)
  have hκa : κ = κf ⟨a, ha⟩ := tendsto_nhds_unique hκ (hκf ⟨a, ha⟩)
  have hκa' : κ' = κf ⟨a', ha'⟩ := tendsto_nhds_unique hκ' (hκf ⟨a', ha'⟩)
  have hhat : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      ∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ) = 0 := by
    intro χ hχ
    refine tendsto_nhds_unique ?_ (hF χ hχ)
    have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) ↦
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hfc : (κf ⟨a, ha⟩ : ℂ) = (κf ⟨a', ha'⟩ : ℂ) :=
    eq_of_sum_char_mul_eq_zero (fun s ↦ (κf s : ℂ)) hhat ⟨a, ha⟩ ⟨a', ha'⟩
  rw [hκa, hκa']
  exact_mod_cast hfc

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1970; norm-residue child. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
          / (N : ℂ))
        Filter.atTop (nhds 0)) :
    ∃ κ C' : ℝ, ∀ a ∈ S, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c)} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  choose κf C'f hκf using exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c
  choose κlim hκlim using exists_tendsto_cardNormLeResidue_div K c
  have hκfeq : ∀ a : ZMod c, κf a = κlim a := fun a ↦
    tendsto_nhds_unique
      (tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos (hκf a)) (hκlim a)
  refine ⟨κlim ((1 : (ZMod c)ˣ) : ZMod c), ∑ b : ZMod c, |C'f b|, fun a ha N hN ↦ ?_⟩
  have hconst : κlim ((a : (ZMod c)ˣ) : ZMod c) = κlim ((1 : (ZMod c)ˣ) : ZMod c) :=
    cardNormLeResidue_density_eq_of_mem_subgroup hF ha (one_mem S)
      (hκlim ((a : (ZMod c)ˣ) : ZMod c)) (hκlim ((1 : (ZMod c)ˣ) : ZMod c))
  rw [← hconst, ← hκfeq ((a : (ZMod c)ˣ) : ZMod c)]
  refine (hκf ((a : (ZMod c)ˣ) : ZMod c) N hN).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  exact (le_abs_self _).trans (Finset.single_le_sum
    (f := fun b ↦ |C'f b|) (fun b _ ↦ abs_nonneg _) (Finset.mem_univ _))

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2027; norm-residue child. -/
def cardNormLeResidueClass {K : Type*} [Field K] [NumberField K] (c : ℕ) (y : ZMod c)
    (C : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = C}

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2035; norm-residue child. -/
theorem exists_tendsto_cardNormLeResidueClass_div {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (y : ZMod c) (C : ClassGroup (𝓞 K)) :
    ∃ κ : ℝ, Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by
  obtain ⟨κ, C', hκ⟩ := exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c y C
  exact ⟨κ, tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos hκ⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2046; norm-residue child. -/
theorem tendsto_cardNormLeResidue_div_eq_sum_class {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (y : ZMod c) {κ : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c y N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (κf : ClassGroup (𝓞 K) → ℝ)
    (hκf : ∀ C, Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κf C))) :
    κ = ∑ C : ClassGroup (𝓞 K), κf C := by
  refine tendsto_nhds_unique hκ ?_
  have hsum := tendsto_finsetSum Finset.univ fun C (_ : C ∈ Finset.univ) ↦ hκf C
  refine hsum.congr fun N ↦ ?_
  rw [cardNormLeResidue, card_norm_le_residue_eq_sum_class c y N, Nat.cast_sum, Finset.sum_div]
  rfl

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2063; norm-residue child. -/
def cardNormLeResidueClassDvd {K : Type*} [Field K] [NumberField K] (c : ℕ)
    (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c) (D : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {J : (Ideal (𝓞 K))⁰ // (𝔟 : Ideal (𝓞 K)) ∣ (J : Ideal (𝓞 K)) ∧
    ((Ideal.absNorm (J : Ideal (𝓞 K)) ≤ N ∧
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 J = D)}

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2074; norm-residue child. -/
theorem cardNormLeResidueClass_eq_dvd {K : Type*} [Field K] [NumberField K] (c : ℕ)
    [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) (N : ℕ) :
    cardNormLeResidueClass c x C N =
      cardNormLeResidueClassDvd c 𝔟 (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
        (C * ClassGroup.mk0 𝔟) (N * Ideal.absNorm (𝔟 : Ideal (𝓞 K))) := by
  classical
  have hNb : 0 < Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  rw [cardNormLeResidueClass, cardNormLeResidueClassDvd]
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr
    (((Equiv.dvd 𝔟).subtypeEquiv (fun I ↦ ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun J : (Ideal (𝓞 K))⁰ ↦ 𝔟 ∣ J) _))
  have hnorm : Ideal.absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) * Ideal.absNorm (I : Ideal (𝓞 K)) := by
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]
  have hcls : ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = ClassGroup.mk0 I * ClassGroup.mk0 𝔟 := by
    rw [Equiv.dvd_apply, map_mul, mul_comm]
  have hle : (Ideal.absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
      N * Ideal.absNorm (𝔟 : Ideal (𝓞 K))) ↔ (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N) := by
    rw [hnorm, mul_comm (Ideal.absNorm (𝔟 : Ideal (𝓞 K))) (Ideal.absNorm (I : Ideal (𝓞 K))),
      Nat.mul_le_mul_right_iff hNb]
  have hres : (((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = x) ↔
      (((Ideal.absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ZMod c)) =
        x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := by
    rw [hnorm, Nat.cast_mul, mul_comm ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)), hu.mul_left_inj]
  have hcl : (ClassGroup.mk0 I = C) ↔
      (ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = C * ClassGroup.mk0 𝔟) := by
    rw [hcls, mul_left_inj]
  rw [← hle, ← hres, ← hcl]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3178; norm-residue child. -/
theorem exists_sub_mul_rpow_le_of_div {f : ℕ → ℝ} {κ C₀ : ℝ} {d NB : ℕ}
    (hdpos : 0 < d) (hNB : 0 < NB) (hf0 : f 0 = 0)
    (hbound : ∀ M : ℕ, 1 ≤ M → |f M - κ * M| ≤ C₀ * (M : ℝ) ^ (1 - (d : ℝ)⁻¹)) :
    ∃ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |f (N / NB) - κ / (NB : ℝ) * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
  have hexp : (0 : ℝ) ≤ 1 - (d : ℝ)⁻¹ := by
    have : (d : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by exact_mod_cast hdpos)]; exact_mod_cast hdpos
    linarith
  refine ⟨|C₀| + |κ|, fun N hN ↦ ?_⟩
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1exp : (1 : ℝ) ≤ (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := Real.one_le_rpow hNR hexp
  set M : ℕ := N / NB with hMdef
  rw [show f M - κ / (NB : ℝ) * N = (f M - κ * M) + (κ * M - κ / (NB : ℝ) * N) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [add_mul]
  gcongr ?_ + ?_
  · rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0, hf0, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
      positivity
    · calc |f M - κ * M| ≤ C₀ * (M : ℝ) ^ (1 - (d : ℝ)⁻¹) := hbound M hMpos
        _ ≤ |C₀| * (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
            refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
            exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.div_le_self N NB) hexp
  · have hMlt : (N : ℝ) / (NB : ℝ) - (M : ℝ) < 1 := by
      have hlt : N < (M + 1) * NB := by
        have hmod : N = NB * M + N % NB := by rw [hMdef]; exact (Nat.div_add_mod N NB).symm
        nlinarith [hmod, Nat.mod_lt N hNB]
      have hltR : (N : ℝ) < ((M : ℝ) + 1) * NB := by exact_mod_cast hlt
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      nlinarith [hltR]
    have hMle : (M : ℝ) ≤ (N : ℝ) / (NB : ℝ) := by
      rw [le_div_iff₀ (by positivity)]; exact_mod_cast Nat.div_mul_le_self N NB
    have hnn : (0 : ℝ) ≤ (N : ℝ) / NB - M := by linarith
    have heq : |κ * (M : ℝ) - κ / (NB : ℝ) * N| = |κ| * ((N : ℝ) / NB - M) := by
      rw [show κ * (M : ℝ) - κ / (NB : ℝ) * N = -(κ * ((N : ℝ) / NB - M)) by field_simp; ring,
        abs_neg, abs_mul, abs_of_nonneg hnn]
    rw [heq]
    calc |κ| * ((N : ℝ) / NB - M) ≤ |κ| * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ |κ| * (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hN1exp (abs_nonneg _)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2109; norm-residue child. -/
theorem Nat.le_iff_le_mul_div_of_dvd {a m : ℕ} (hm : 0 < m) (hd : m ∣ a) (N : ℕ) :
    a ≤ N ↔ a ≤ m * (N / m) := by
  obtain ⟨k, rfl⟩ := hd
  refine ⟨fun h ↦ ?_, fun h ↦ le_trans h (Nat.mul_div_le N m)⟩
  exact Nat.mul_le_mul_left m ((Nat.le_div_iff_mul_le hm).mpr (by rwa [mul_comm] at h))

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2120; norm-residue child. -/
theorem cardNormLeResidueClassDvd_floor_collapse {K : Type*} [Field K]
    [NumberField K] (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c)
    (D : ClassGroup (𝓞 K)) (N : ℕ) :
    cardNormLeResidueClassDvd c 𝔟 y D N = cardNormLeResidueClassDvd c 𝔟 y D
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) * (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K)))) := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  rw [cardNormLeResidueClassDvd, cardNormLeResidueClassDvd]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun J ↦ and_congr_right fun hb ↦
    and_congr_left fun _ ↦ and_congr_left fun _ ↦
      Nat.le_iff_le_mul_div_of_dvd hNB (map_dvd Ideal.absNorm hb) N)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3055; norm-residue child. -/
theorem cardNormLeResidueClassDvd_eq_div {K : Type*} [Field K] [NumberField K] (c : ℕ)
    [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰) (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    {xC y : ZMod c} {CC D : ClassGroup (𝓞 K)}
    (hxmul : xC * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c) = y)
    (hCmul : CC * ClassGroup.mk0 𝔟 = D) (N : ℕ) :
    cardNormLeResidueClassDvd c 𝔟 y D N
      = cardNormLeResidueClass c xC CC (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K))) := by
  rw [cardNormLeResidueClassDvd_floor_collapse c 𝔟 y D N,
    cardNormLeResidueClass_eq_dvd c 𝔟 hu xC CC (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K))),
    hxmul, hCmul, mul_comm]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3072; norm-residue child. -/
theorem cardNormLeResidueClassDvd_div_density_routeA {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (y : ZMod c) (D : ClassGroup (𝓞 K)) {κCC : ℝ}
    (hκCC : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c
        (y * (↑hu.unit⁻¹ : ZMod c)) (D * (ClassGroup.mk0 𝔟)⁻¹) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κCC)) :
    Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κCC / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ))) := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  set u : (ZMod c)ˣ := hu.unit with hudef
  have hu_spec : (↑u : ZMod c) = (NB : ZMod c) := hu.unit_spec
  set xC : ZMod c := y * (↑u⁻¹ : ZMod c) with hxC
  set CC : ClassGroup (𝓞 K) := D * (ClassGroup.mk0 𝔟)⁻¹ with hCC
  have hxmul : xC * (NB : ZMod c) = y := by
    rw [hxC, ← hu_spec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hCmul : CC * ClassGroup.mk0 𝔟 = D := by rw [hCC, inv_mul_cancel_right]
  have hcount : ∀ N : ℕ, cardNormLeResidueClassDvd c 𝔟 y D N
      = cardNormLeResidueClass c xC CC (N / NB) :=
    fun N ↦ cardNormLeResidueClassDvd_eq_div c 𝔟 hu hxmul hCmul N
  refine Filter.Tendsto.congr (fun N ↦ by rw [hcount N]) ?_
  have hgN : Filter.Tendsto (fun N : ℕ ↦ (N / NB : ℕ)) Filter.atTop Filter.atTop :=
    Nat.tendsto_div_const_atTop hNB.ne'
  have hratio : Filter.Tendsto (fun N : ℕ ↦ ((N / NB : ℕ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds (1 / (NB : ℝ))) := by
    have hsub : Filter.Tendsto (fun N : ℕ ↦ ((N % NB : ℕ) : ℝ) / (N : ℝ))
        Filter.atTop (nhds 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ by positivity)
        (Filter.Eventually.of_forall fun N ↦ ?_)
        (tendsto_const_div_atTop_nhds_zero_nat (NB : ℝ))
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · simp [hN0]
      · have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
        rw [div_le_div_iff_of_pos_right hNposR]
        exact_mod_cast (Nat.mod_lt N hNB).le
    have hkey : ∀ N : ℕ, 1 ≤ N → ((N / NB : ℕ) : ℝ) / (N : ℝ)
        = (1 - ((N % NB : ℕ) : ℝ) / (N : ℝ)) / (NB : ℝ) := by
      intro N hN
      have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hdm : ((N / NB : ℕ) : ℝ) * (NB : ℝ) + ((N % NB : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast Nat.div_add_mod' N NB
      field_simp
      nlinarith [hdm]
    have hlim : Filter.Tendsto (fun N : ℕ ↦ (1 - ((N % NB : ℕ) : ℝ) / (N : ℝ)) / (NB : ℝ))
        Filter.atTop (nhds ((1 - 0) / (NB : ℝ))) :=
      (tendsto_const_nhds.sub hsub).div_const (NB : ℝ)
    refine (hlim.congr' ?_).mono_right (by rw [sub_zero])
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN using (hkey N hN).symm
  have hcomp : Filter.Tendsto
      (fun N : ℕ ↦ (cardNormLeResidueClass c xC CC (N / NB) : ℝ) / ((N / NB : ℕ) : ℝ))
      Filter.atTop (nhds κCC) := hκCC.comp hgN
  have hprod := hcomp.mul hratio
  rw [show κCC * (1 / (NB : ℝ)) = κCC / (NB : ℝ) by ring] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (NB + 1)] with N hN
  have hgpos : 0 < N / NB := Nat.div_pos (le_trans (by omega) hN) hNB
  have hgR : ((N / NB : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2936; norm-residue child. -/
theorem tendsto_count_div_of_cone_bridge {K : Type*} [Field K] [NumberField K]
    (NJ : ℕ) (hNJ : 0 < NJ) (κ₀ C' : ℝ) (cnt : ℕ → ℕ) (coneR : ℝ → ℝ)
    (hbridge : ∀ N : ℕ, (cnt N : ℝ) * (torsionOrder K : ℝ) = coneR ((N * NJ : ℕ) : ℝ))
    (hcone : ∀ S : ℝ, 1 ≤ S → |coneR S - κ₀ * S| ≤ C' * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) :
    Filter.Tendsto (fun N : ℕ ↦ (cnt N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ₀ * (NJ : ℝ) / (torsionOrder K : ℝ))) := by
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  have htors : (0 : ℝ) < torsionOrder K := by
    exact_mod_cast (torsionOrder K).pos_of_ne_zero (torsionOrder_ne_zero K)
  refine tendsto_div_atTop_of_sub_mul_rpow_le (C' := |C'| * (NJ : ℝ) / (torsionOrder K : ℝ))
    (d := d) hdpos (fun N hN ↦ ?_)
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNJN : (1 : ℝ) ≤ ((N * NJ : ℕ) : ℝ) := by
    rw [Nat.cast_mul]; exact one_le_mul_of_one_le_of_one_le hNR (by exact_mod_cast hNJ)
  have hkey := hcone ((N * NJ : ℕ) : ℝ) hNJN
  rw [← hbridge N, Nat.cast_mul] at hkey
  rw [show (cnt N : ℝ) - κ₀ * (NJ : ℝ) / (torsionOrder K : ℝ) * N
      = ((cnt N : ℝ) * (torsionOrder K : ℝ) - κ₀ * ((N : ℝ) * (NJ : ℝ))) / (torsionOrder K : ℝ) by
    field_simp]
  rw [abs_div, abs_of_pos htors, div_le_iff₀ htors]
  refine hkey.trans ?_
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have hNJpow : (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) ≤ (NJ : ℝ) :=
    calc (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) ≤ (NJ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hNJ)
            (by simp only [tsub_le_iff_right, le_add_iff_nonneg_right]; positivity)
      _ = (NJ : ℝ) := Real.rpow_one _
  have hgoalRHS : |C'| * (NJ : ℝ) / (torsionOrder K : ℝ) * (N : ℝ) ^ (1 - (d : ℝ)⁻¹) *
      (torsionOrder K : ℝ) = |C'| * ((N : ℝ) ^ (1 - (d : ℝ)⁻¹) * (NJ : ℝ)) := by
    field_simp
  rw [hgoalRHS]
  rw [mul_comm ((N : ℝ) ^ (1 - (d : ℝ)⁻¹)) ((NJ : ℝ) ^ (1 - (d : ℝ)⁻¹)),
    mul_comm ((N : ℝ) ^ (1 - (d : ℝ)⁻¹)) (NJ : ℝ), ← mul_assoc, ← mul_assoc]
  gcongr
  exact le_abs_self _

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2978; norm-residue child. -/
theorem card_isPrincipal_dvd_norm_le_residue_natBound {K : Type*} [Field K] [NumberField K]
    (I₀ : (Ideal (𝓞 K))⁰) (m b M : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ M ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} * torsionOrder K =
      Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ (M : ℝ) ∧
        ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} := by
  rw [← card_isPrincipal_dvd_norm_le_residue I₀ m b (M : ℝ)]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ by rw [Nat.cast_le])

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2891; norm-residue child. -/
theorem card_principalize_dvd {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c) (N : ℕ) (D : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = D⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
    cardNormLeResidueClassDvd c 𝔟 y D N
    = Nat.card {I : (Ideal (𝓞 K))⁰ // (𝔟 * J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
        (IsPrincipal (I : Ideal (𝓞 K)) ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((y.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
  classical
  rw [cardNormLeResidueClassDvd]
  have hdvd : ∀ I : (Ideal (𝓞 K))⁰, ((𝔟 * J : Ideal (𝓞 K)) ∣ (J * I : Ideal (𝓞 K)))
      ↔ ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) := by
    intro I
    rw [mul_comm (𝔟 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)),
      mul_dvd_mul_iff_left (nonZeroDivisors.coe_ne_zero J)]
  refine Nat.card_congr
    (((Equiv.dvd J).subtypeEquiv (fun I ↦ ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtype (p := fun a : (Ideal (𝓞 K))⁰ ↦ J ∣ a)
        (q := fun I' : (Ideal (𝓞 K))⁰ ↦ (𝔟 * J : Ideal (𝓞 K)) ∣ (I' : Ideal (𝓞 K)) ∧
          IsPrincipal (I' : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I' : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I' : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((y.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))
        (fun {a} hq ↦ by
          beta_reduce at hq ⊢
          rw [nonZeroDivisors_dvd_iff_dvd_coe]
          exact dvd_trans (Dvd.intro_left _ rfl) hq.1)))
  simp only [Equiv.dvd_apply, Submonoid.coe_mul]
  rw [show ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = D))
      ↔ (((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = D) ∧
        (𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) by tauto,
    principalize_iff c y N D J I hJ hNJ]
  rw [show ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) ↔
      ((𝔟 * J : Ideal (𝓞 K)) ∣ ((J : Ideal (𝓞 K)) * (I : Ideal (𝓞 K)))) from (hdvd I).symm]
  tauto

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2831; norm-residue child. -/
theorem exists_card_idealSet_residue_real_le_dvd {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (hcop : (Ideal.absNorm (𝔟 : Ideal (𝓞 K))).Coprime m) :
    ∃ κ C' : ℝ,
      (∀ S : ℝ, 1 ≤ S →
        |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * S|
          ≤ C' * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) ∧
      (∀ S : ℝ, 1 ≤ S →
        |(Nat.card {a : idealSet K (𝔟 * J) // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
            ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))} : ℝ)
            - (κ / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)) * S|
          ≤ C' * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) := by
  classical
  set d := Module.finrank ℚ K with hd
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  obtain ⟨T, hT⟩ := exists_latticeEquiv_image_idealLattice J
  obtain ⟨T', hT'⟩ := exists_latticeEquiv_image_idealLattice (𝔟 * J)
  obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K
  have hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
      (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 :=
    ⟨mc, M, φ, hφ, hcovraw⟩
  choose CJ hCJ using fun p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) ↦
    exists_card_residue_fibre_sub_mul_rpow_le_explicit m hm b J T hT hcov p.1 p.2
  choose CB hCB using fun p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) ↦
    exists_card_fibre_dvd_residue_sub_mul_rpow_le m hm b J 𝔟 hcop T T' hT hT' hcov p.1 p.2
  set L : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) → ℝ :=
    fun p ↦ if (∃ a : idealSet K J,
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = p.1) ∧
        ((fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = p.2) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
      then MeasureTheory.volume.real ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ p.1, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ p.1, 0 ≤ y (Sum.inl w))})
        / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
          : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
      else 0 with hL
  refine ⟨∑ p, L p, ∑ p, (|CJ p| + |CB p|), ?_, ?_⟩
  · intro S hS
    refine card_residue_sum_bound_aux m b J T S hS L (fun p ↦ |CJ p| + |CB p|)
      (fun p tN htN ↦ ?_)
    refine le_trans (hCJ p tN htN) ?_
    gcongr
    exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  · intro S hS
    rw [show (∑ p, L p) / (NB : ℝ) = ∑ p, (L p / (NB : ℝ)) by rw [Finset.sum_div]]
    refine card_residue_sum_bound_aux m b (𝔟 * J) T S hS (fun p ↦ L p / (NB : ℝ))
      (fun p ↦ |CJ p| + |CB p|) (fun p tN htN ↦ ?_)
    refine le_trans (hCB p tN htN) ?_
    gcongr
    exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:2997; norm-residue child. -/
theorem cardNormLeResidueClassDvd_div_density {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (y : ZMod c) (D : ClassGroup (𝓞 K)) {κfull : ℝ}
    (hκfull : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κfull)) :
    Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κfull / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ))) := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  obtain ⟨J, hJ, hJcop⟩ := exists_mk0_eq_absNorm_coprime D⁻¹ NB hNB
  set NJ : ℕ := Ideal.absNorm (J : Ideal (𝓞 K)) with hNJdef
  have hNJ : 0 < NJ := Ideal.absNorm_pos_of_nonZeroDivisors J
  have hNBc : NB.Coprime c := by rw [hNBdef, ZMod.isUnit_iff_coprime] at hu; exact hu
  have hcop : NB.Coprime (c * NJ) := Nat.Coprime.mul_right hNBc (hNJdef ▸ hJcop.symm)
  haveI : NeZero (c * NJ) := ⟨Nat.mul_ne_zero (NeZero.ne c) hNJ.ne'⟩
  have hm : ((c * NJ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (c * NJ))
  obtain ⟨κ, C', hJcone, h𝔟Jcone⟩ :=
    exists_card_idealSet_residue_real_le_dvd (c * NJ) hm (y.val * NJ) J 𝔟 hcop
  set coneJ : ℝ → ℝ := fun S ↦ (Nat.card {a : idealSet K J //
    mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod (c * NJ))
        = ((y.val * NJ : ℕ) : ZMod (c * NJ)))} : ℝ)
    with hconeJ
  set cone𝔟J : ℝ → ℝ := fun S ↦ (Nat.card {a : idealSet K (𝔟 * J) //
    mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
      ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod (c * NJ))
        = ((y.val * NJ : ℕ) : ZMod (c * NJ)))} : ℝ) with hcone𝔟J
  have hbridgeJ : ∀ N : ℕ, (cardNormLeResidueClass c y D N : ℝ) * (torsionOrder K : ℝ)
      = coneJ ((N * NJ : ℕ) : ℝ) := fun N ↦ by
    rw [hconeJ, ← Nat.cast_mul, cardNormLeResidueClass, card_principalize c y N D J hJ hNJ,
      card_isPrincipal_dvd_norm_le_residue_natBound J (c * NJ) (y.val * NJ) (N * NJ)]
  have hbridge𝔟J : ∀ N : ℕ,
      (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) * (torsionOrder K : ℝ)
      = cone𝔟J ((N * NJ : ℕ) : ℝ) := fun N ↦ by
    rw [hcone𝔟J, ← Nat.cast_mul, card_principalize_dvd c 𝔟 y N D J hJ hNJ, ← Submonoid.coe_mul,
      card_isPrincipal_dvd_norm_le_residue_natBound (𝔟 * J) (c * NJ) (y.val * NJ) (N * NJ)]
  have hJdens : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ * (NJ : ℝ) / (torsionOrder K : ℝ))) :=
    tendsto_count_div_of_cone_bridge NJ hNJ κ C' (cardNormLeResidueClass c y D) coneJ hbridgeJ
      (fun S hS ↦ by rw [hconeJ]; exact hJcone S hS)
  have hκfull_eq : κfull = κ * (NJ : ℝ) / (torsionOrder K : ℝ) :=
    tendsto_nhds_unique hκfull hJdens
  have h𝔟Jdens : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ / (NB : ℝ) * (NJ : ℝ) / (torsionOrder K : ℝ))) :=
    tendsto_count_div_of_cone_bridge NJ hNJ (κ / (NB : ℝ)) C' (cardNormLeResidueClassDvd c 𝔟 y D)
      cone𝔟J hbridge𝔟J (fun S hS ↦ by rw [hcone𝔟J]; exact h𝔟Jcone S hS)
  rw [show κfull / (NB : ℝ) = κ / (NB : ℝ) * (NJ : ℝ) / (torsionOrder K : ℝ) by
    rw [hκfull_eq]; ring]
  exact h𝔟Jdens

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3143; norm-residue child. -/
theorem tendsto_cardNormLeResidueClass_div_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) {κ : ℝ}
    (hκ : Filter.Tendsto (fun M : ℕ ↦ (cardNormLeResidueClass c x C M : ℝ) / (M : ℝ))
      Filter.atTop (nhds κ)) :
    Filter.Tendsto (fun M : ℕ ↦ (cardNormLeResidueClass c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) (C * ClassGroup.mk0 𝔟) M : ℝ) / (M : ℝ))
      Filter.atTop (nhds κ) := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  set y : ZMod c := x * (NB : ZMod c) with hy
  set D : ClassGroup (𝓞 K) := C * ClassGroup.mk0 𝔟 with hD
  obtain ⟨κ', hκ'⟩ := exists_tendsto_cardNormLeResidueClass_div (K := K) c y D
  suffices heq : κ' = κ by rwa [heq] at hκ'
  set u : (ZMod c)ˣ := hu.unit with hudef
  have hu_spec : (↑u : ZMod c) = (NB : ZMod c) := hu.unit_spec
  have hxC : y * (↑u⁻¹ : ZMod c) = x := by
    rw [hy, ← hu_spec, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hCC : D * (ClassGroup.mk0 𝔟)⁻¹ = C := by rw [hD, mul_inv_cancel_right]
  have hL2 : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ' / (NB : ℝ))) :=
    cardNormLeResidueClassDvd_div_density c 𝔟 hu y D hκ'
  have hL3 : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ / (NB : ℝ))) := by
    refine cardNormLeResidueClassDvd_div_density_routeA c 𝔟 hu y D (κCC := κ) ?_
    rwa [hxC, hCC]
  have hdiv : κ' / (NB : ℝ) = κ / (NB : ℝ) := tendsto_nhds_unique hL2 hL3
  exact (div_left_inj' hNB0).mp hdiv

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3228; norm-residue child. -/
theorem cardNormLeResidueClassDvd_sub_mul_rpow_le {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (y : ZMod c) (D : ClassGroup (𝓞 K)) {κfull : ℝ}
    (hκfull : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κfull)) :
    ∃ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) -
          (κfull / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)) * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  set u : (ZMod c)ˣ := hu.unit with hudef
  have hu_spec : (↑u : ZMod c) = (NB : ZMod c) := hu.unit_spec
  set xC : ZMod c := y * (↑u⁻¹ : ZMod c) with hxC
  set CC : ClassGroup (𝓞 K) := D * (ClassGroup.mk0 𝔟)⁻¹ with hCC
  have hxmul : xC * (NB : ZMod c) = y := by
    rw [hxC, ← hu_spec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hCmul : CC * ClassGroup.mk0 𝔟 = D := by
    rw [hCC, inv_mul_cancel_right]
  obtain ⟨κC, C₀, hbound⟩ :=
    exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c xC CC
  have hκC : Filter.Tendsto (fun M : ℕ ↦ (cardNormLeResidueClass c xC CC M : ℝ) / (M : ℝ))
      Filter.atTop (nhds κC) :=
    tendsto_div_atTop_of_sub_mul_rpow_le (C' := C₀) (d := d) hdpos
      (fun N hN ↦ by simpa only [cardNormLeResidueClass] using hbound N hN)
  have hκCfull : κC = κfull := by
    refine tendsto_nhds_unique ?_ hκfull
    have := tendsto_cardNormLeResidueClass_div_transfer c 𝔟 hu xC CC hκC
    rw [hxmul, hCmul] at this
    exact this
  subst hκCfull
  refine (exists_sub_mul_rpow_le_of_div hdpos hNB
    (f := fun M ↦ (cardNormLeResidueClass c xC CC M : ℝ)) ?_
    (fun M hM ↦ by simpa only [cardNormLeResidueClass] using hbound M hM)).imp
    fun C' hC' N hN ↦ by
      rw [cardNormLeResidueClassDvd_eq_div c 𝔟 hu hxmul hCmul N]; exact hC' N hN
  simp only [cardNormLeResidueClass, Nat.cast_eq_zero, Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨I, hI, _⟩ ↦ nonZeroDivisors.coe_ne_zero I
    (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp hI.1))⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3280; norm-residue child. -/
theorem cardNormLeResidueClass_density_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c x C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) (C * ClassGroup.mk0 𝔟) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := Ideal.absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  set y : ZMod c := x * (NB : ZMod c) with hy
  set D : ClassGroup (𝓞 K) := C * ClassGroup.mk0 𝔟 with hD
  have hκd : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ' / (NB : ℝ))) :=
    (cardNormLeResidueClassDvd_sub_mul_rpow_le c 𝔟 hu y D hκ').elim fun _ hC' ↦
      tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos hC'
  have hAlim : Filter.Tendsto
      (fun M : ℕ ↦ (cardNormLeResidueClass c x C M : ℝ) / (M : ℝ))
      Filter.atTop (nhds ((NB : ℝ) * (κ' / (NB : ℝ)))) := by
    have hcomp : Filter.Tendsto (fun M : ℕ ↦ M * NB) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun M ↦ Nat.le_mul_of_pos_right M hNB) Filter.tendsto_id
    have hd2 : Filter.Tendsto
        (fun M : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D (M * NB) : ℝ) / ((M * NB : ℕ) : ℝ))
        Filter.atTop (nhds (κ' / (NB : ℝ))) := hκd.comp hcomp
    refine (hd2.const_mul (NB : ℝ)).congr fun M ↦ ?_
    rw [cardNormLeResidueClass_eq_dvd c 𝔟 hu x C M, ← hy, ← hD]
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · simp [hM0]
    · have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
      rw [Nat.cast_mul]
      field_simp
      ring
  rw [tendsto_nhds_unique hκ hAlim, mul_div_cancel₀ _ hNB0]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3322; norm-residue child. -/
theorem cardNormLeResidue_density_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c x N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  choose κf hκf using fun C ↦ exists_tendsto_cardNormLeResidueClass_div (K := K) c x C
  choose κf' hκf' using fun C ↦
    exists_tendsto_cardNormLeResidueClass_div (K := K) c
      (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) C
  have hsplit : κ = ∑ C : ClassGroup (𝓞 K), κf C :=
    tendsto_cardNormLeResidue_div_eq_sum_class c x hκ κf hκf
  have hsplit' : κ' = ∑ C : ClassGroup (𝓞 K), κf' C :=
    tendsto_cardNormLeResidue_div_eq_sum_class c
      (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) hκ' κf' hκf'
  have htrans : ∀ C : ClassGroup (𝓞 K), κf C = κf' (C * ClassGroup.mk0 𝔟) := fun C ↦
    cardNormLeResidueClass_density_transfer c 𝔟 hu x C (hκf C) (hκf' (C * ClassGroup.mk0 𝔟))
  rw [hsplit, hsplit', Finset.sum_congr rfl fun C _ ↦ htrans C]
  exact Equiv.sum_comp (Equiv.mulRight (ClassGroup.mk0 𝔟)) κf'

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3353; norm-residue child. -/
theorem cardNormLeResidue_density_const_of_realized
    {K : Type*} [Field K] [NumberField K] {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    {a a' : (ZMod c)ˣ} (ha : a ∈ S) (ha' : a' ∈ S) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a' : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  obtain ⟨𝔟, h𝔟⟩ := hS a ha
  obtain ⟨𝔟', h𝔟'⟩ := hS a' ha'
  have hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := h𝔟 ▸ a.isUnit
  have hu' : IsUnit ((Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) := h𝔟' ▸ a'.isUnit
  obtain ⟨κ₁, hκ₁⟩ := exists_tendsto_cardNormLeResidue_div K c (1 : ZMod c)
  have hone_eq : (1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c) = (a : ZMod c) := by
    rw [one_mul, h𝔟]
  have hone_eq' : (1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c) = (a' : ZMod c) := by
    rw [one_mul, h𝔟']
  have hκ_a : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by rwa [hone_eq]
  have hκ_a' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ') := by rwa [hone_eq']
  have h1 : κ₁ = κ := cardNormLeResidue_density_transfer c 𝔟 hu (1 : ZMod c) hκ₁ hκ_a
  have h2 : κ₁ = κ' := cardNormLeResidue_density_transfer c 𝔟' hu' (1 : ZMod c) hκ₁ hκ_a'
  rw [← h1, h2]

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:3397; norm-residue child. -/
theorem tendsto_sum_char_mul_cardNormLeResidue_div_of_realized
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    (χ : S →* ℂˣ) (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds 0) := by
  classical
  choose κf hκf using fun s : S ↦
    exists_tendsto_cardNormLeResidue_div K c ((s : (ZMod c)ˣ) : ZMod c)
  have hconst : ∀ s : S, κf s = κf 1 := fun s ↦
    cardNormLeResidue_density_const_of_realized hS s.2 (one_mem S) (hκf s) (hκf 1)
  have hlim : Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))) := by
    have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) ↦
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [Function.comp_apply, cardNormLeResidue]
    push_cast
    ring
  have hval : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ)) = 0 := by
    have hrw : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))
        = (∑ s : S, ((χ s : ℂˣ) : ℂ)) * (κf 1 : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [hconst s]
    rw [hrw, sum_char_self_eq_zero_of_ne_one hχ, zero_mul]
  rwa [hval] at hlim

end Cox.Chebotarev
