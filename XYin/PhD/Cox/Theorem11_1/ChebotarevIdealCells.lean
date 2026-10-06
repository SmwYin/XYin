/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs
import XYin.PhD.Cox.Theorem11_1.ChebotarevLatticeCounting

/-! # Ideal-lattice residue cells
Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`.
-/
noncomputable section
open NumberField Set Submodule
open NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace
open scoped NNReal nonZeroDivisors Pointwise
namespace Cox.Chebotarev

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:393. -/
theorem natCast_algebraNorm_add_nsmul_mul {K : Type*} [Field K] [NumberField K]
    (M : ℕ) (x y : 𝓞 K) :
    ((Algebra.norm ℤ (x + (M : 𝓞 K) * y) : ℤ) : ZMod M) = ((Algebra.norm ℤ x : ℤ) : ZMod M) := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, Int.cast_det, Int.cast_det]
  congr 1
  rw [show (M : 𝓞 K) * y = M • y from (nsmul_eq_mul _ _).symm, map_add, map_nsmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Int.cast_add]
  rw [show (((M • (Algebra.leftMulMatrix b) y i j) : ℤ) : ZMod M) = 0 by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul], add_zero]

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:414. -/
theorem norm_eq_prod_real_emb_mul_prod_complex {K : Type*} [Field K] [NumberField K]
    (y : K) :
    ((Algebra.norm ℚ y : ℝ)) =
      (∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y) *
        (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2) := by
  classical
  have hcc : ((Algebra.norm ℚ y : ℝ) : ℂ) =
      ((∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y : ℝ) : ℂ) *
        ((∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2 : ℝ) : ℂ) := by
    have hperplace : ∀ w : InfinitePlace K,
        ∏ ψ ∈ Finset.univ.filter (fun ψ : K →+* ℂ ↦ mk ψ = w), ψ y =
          if hw : IsReal w then ((embedding_of_isReal hw y : ℝ) : ℂ)
          else (‖(embedding w) y‖ ^ 2 : ℝ) := by
      intro w
      have hfilter : Finset.univ.filter (fun ψ : K →+* ℂ ↦ mk ψ = w)
          = {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
          star_involutive.eq_iff]
      rw [hfilter]
      by_cases hw : IsReal w
      · rw [dif_pos hw, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw),
          Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.prod_singleton,
          embedding_of_isReal_apply hw]
      · rw [dif_neg hw, Finset.prod_pair]
        · rw [ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
          norm_cast
          rw [Complex.normSq_eq_norm_sq]
        · rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]; exact hw
    have hemb : (algebraMap ℚ ℂ) (Algebra.norm ℚ y) = ∏ ψ : K →+* ℂ, ψ y := by
      rw [Algebra.norm_eq_prod_embeddings ℚ ℂ y]
      exact (Fintype.prod_equiv RingHom.equivRatAlgHom (fun ψ : K →+* ℂ ↦ ψ y)
        (fun σ : K →ₐ[ℚ] ℂ ↦ σ y) (fun ψ ↦ by simp [RingHom.equivRatAlgHom_apply])).symm
    rw [show ((Algebra.norm ℚ y : ℝ) : ℂ) = (algebraMap ℚ ℂ) (Algebra.norm ℚ y) by
        rw [eq_ratCast (algebraMap ℚ ℂ), Complex.ofReal_ratCast], hemb,
      ← Finset.prod_fiberwise (g := fun ψ : K →+* ℂ ↦ mk ψ) (f := fun ψ ↦ ψ y) Finset.univ]
    simp_rw [hperplace]
    rw [prod_eq_prod_mul_prod]
    congr 1
    · rw [Finset.prod_congr rfl (fun w _ ↦ by rw [dif_pos w.2]), Complex.ofReal_prod]
    · rw [Finset.prod_congr rfl (fun w _ ↦ by rw [dif_neg (not_isReal_iff_isComplex.mpr w.2)]),
        Complex.ofReal_prod]
  exact_mod_cast hcc

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:462. -/
theorem prod_eq_neg_one_pow_card_mul_prod_abs {ι : Type*} [Fintype ι]
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι)
    (f : ι → R) (hpos : ∀ w ∉ s, 0 < f w) (hneg : ∀ w ∈ s, f w < 0) :
    (∏ w, f w) = (-1) ^ (s.card) * (∏ w, |f w|) := by
  classical
  rw [← Finset.prod_mul_prod_compl s f, ← Finset.prod_mul_prod_compl s (fun w ↦ |f w|),
    show ((-1 : R)) ^ s.card = ∏ w ∈ s, (-1 : R) by rw [Finset.prod_const],
    ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_congr rfl (fun w hw ↦ by rw [neg_one_mul, abs_of_neg (hneg w hw), neg_neg])
  · exact Finset.prod_congr rfl (fun w hw ↦ (abs_of_pos (hpos w (Finset.mem_compl.mp hw))).symm)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:479. -/
theorem natAbs_norm_eq_neg_one_pow_mul_norm {K : Type*} [Field K] [NumberField K]
    (y : 𝓞 K) (s : Finset {w : InfinitePlace K // IsReal w})
    (hneg : ∀ w ∈ s, (mixedEmbedding K (y : K)).1 w < 0)
    (hpos : ∀ w ∉ s, 0 < (mixedEmbedding K (y : K)).1 w) :
    ((Algebra.norm ℤ y).natAbs : ℤ) = (-1) ^ (s.card) * (Algebra.norm ℤ y : ℤ) := by
  classical
  have hcoe : ((Algebra.norm ℤ y : ℤ) : ℝ) = Algebra.norm ℚ (y : K) := by
    rw [← Algebra.coe_norm_int]; push_cast; ring
  have hcpx : 0 ≤
      (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (y : K)‖ ^ 2) :=
    Finset.prod_nonneg (fun w _ ↦ sq_nonneg _)
  have hmix : ∀ w : {w : InfinitePlace K // IsReal w},
      embedding_of_isReal w.2 (y : K) = (mixedEmbedding K (y : K)).1 w := fun w ↦ by
    rw [mixedEmbedding_apply_isReal]
  have hneg' : ∀ w ∈ s, embedding_of_isReal w.2 (y : K) < 0 := fun w hw ↦ by
    rw [hmix]; exact hneg w hw
  have hpos' : ∀ w ∉ s, 0 < embedding_of_isReal w.2 (y : K) := fun w hw ↦ by
    rw [hmix]; exact hpos w hw
  have hsign := prod_eq_neg_one_pow_card_mul_prod_abs s
    (fun w : {w : InfinitePlace K // IsReal w} ↦ embedding_of_isReal w.2 (y : K)) hpos' hneg'
  have hnf := norm_eq_prod_real_emb_mul_prod_complex (K := K) (y : K)
  have habs : |((Algebra.norm ℚ (y : K) : ℝ))|
      = (∏ w : {w : InfinitePlace K // IsReal w}, |embedding_of_isReal w.2 (y : K)|) *
        (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (y : K)‖ ^ 2) := by
    rw [hnf, abs_mul, abs_of_nonneg hcpx, Finset.abs_prod]
  have hkeyR : ((Algebra.norm ℚ (y : K) : ℝ))
      = (-1) ^ (s.card) * |((Algebra.norm ℚ (y : K) : ℝ))| := by
    rw [habs]
    conv_lhs => rw [hnf, hsign]
    ring
  have hZ' : (Algebra.norm ℤ y : ℤ) = (-1) ^ (s.card) * ((Algebra.norm ℤ y).natAbs : ℤ) := by
    have hZ : ((Algebra.norm ℤ y : ℤ) : ℝ)
        = ((-1) ^ (s.card) * ((Algebra.norm ℤ y).natAbs : ℤ) : ℤ) := by
      push_cast
      rw [hcoe]
      exact hkeyR
    exact_mod_cast hZ
  conv_rhs => rw [hZ']
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:646. -/
theorem map_span_int_linearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E ≃ₗ[ℝ] F) (S : Set E) :
    f '' (span ℤ S : Set E) = (span ℤ (f '' S) : Set F) := by
  simpa using congrArg SetLike.coe (Submodule.map_span (f.restrictScalars ℤ).toLinearMap S)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:656. -/
theorem cone_normLe_eq_smul_normLeOne {K : Type*} [Field K] [NumberField K] {t : ℝ}
    (ht : 1 ≤ t) :
    {x : mixedSpace K | x ∈ fundamentalCone K ∧
        mixedEmbedding.norm x ≤ t ^ (Module.finrank ℚ K)} = t • normLeOne K := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have htne : t ≠ 0 := ht0.ne'
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, normLeOne, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcone, hnorm⟩
    refine ⟨t⁻¹ • x, ⟨(smul_mem_iff_mem (inv_ne_zero htne)).mpr hcone, ?_⟩, ?_⟩
    · rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr ht0), inv_pow,
        inv_mul_le_one₀ (by positivity)]
      exact hnorm
    · rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
  · rintro ⟨y, ⟨hcone, hnorm⟩, rfl⟩
    refine ⟨(smul_mem_iff_mem htne).mpr hcone, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_of_pos ht0]
    calc t ^ (Module.finrank ℚ K) * mixedEmbedding.norm y
        ≤ t ^ (Module.finrank ℚ K) * 1 :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = t ^ (Module.finrank ℚ K) := mul_one _

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:687. -/
theorem exists_latticeEquiv_image_idealLattice {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ),
      T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
  set I := FractionalIdeal.mk0 K J
  have e : Module.Free.ChooseBasisIndex ℤ I ≃ index K := by
    apply Fintype.equivOfCardEq
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.fractionalIdeal_rank,
      RingOfIntegers.rank, ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
  set c : Module.Basis (index K) ℝ (index K → ℝ) :=
    ((mixedEmbedding.fractionalIdealLatticeBasis K I).map Φ.toLinearEquiv).reindex e with hc
  refine ⟨(Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)), ?_⟩
  have hcrange : Set.range c
      = Φ '' (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
    rw [hc, Module.Basis.range_reindex, ← Set.range_comp]; rfl
  rw [map_span_int_linearEquiv]
  have hrange : ((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)))
      '' (Set.range (Pi.basisFun ℝ (index K))) = Set.range c := by
    rw [← Set.range_comp]
    congr 1; ext i
    simp only [Function.comp_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [hrange, hcrange, ← mixedEmbedding.span_idealLatticeBasis K I]
  exact (map_span_int_linearEquiv Φ.toLinearEquiv _).symm

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:722. -/
theorem exists_lipschitz_cube_cover_hyperplane_slab {ι : Type*} [Fintype ι]
    (j : ι) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (M : ℝ≥0) (φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      LipschitzWith M φ ∧
        {x : ι → ℝ | x j = 0 ∧ ∀ i, |x i| ≤ R} ⊆ φ '' Set.Icc 0 1 := by
  classical
  have hcard : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]; simp
  set σ : Fin (Fintype.card ι - 1) ≃ {i : ι // i ≠ j} :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun c i ↦ if h : i = j then 0 else (2 * R) * c (σ.symm ⟨i, h⟩) - R with hφ
  refine ⟨(2 * R).toNNReal, φ, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun c c' ↦ ?_
    rw [dist_pi_le_iff (by positivity)]
    intro i
    by_cases hij : i = j
    · simp only [hφ, dif_pos hij, dist_self]; positivity
    · simp only [hφ, dif_neg hij]
      have hreorg : (2 * R) * c (σ.symm ⟨i, hij⟩) - R - ((2 * R) * c' (σ.symm ⟨i, hij⟩) - R)
          = (2 * R) * (c (σ.symm ⟨i, hij⟩) - c' (σ.symm ⟨i, hij⟩)) := by ring
      rw [Real.dist_eq, hreorg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * R),
        Real.coe_toNNReal _ (by positivity)]
      gcongr
      rw [← Real.dist_eq]
      exact dist_le_pi_dist c c' (σ.symm ⟨i, hij⟩)
  · rintro x ⟨hxj, hxbd⟩
    rcases eq_or_lt_of_le hR with hR0 | hR0
    · have hx0 : x = 0 := by
        ext i; have := hxbd i; rw [← hR0] at this; exact abs_nonpos_iff.mp this
      refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      ext i; simp only [hφ]
      by_cases hij : i = j
      · rw [dif_pos hij, hx0]; rfl
      · rw [dif_neg hij, hx0]; simp [← hR0]
    · refine ⟨fun k ↦ (x (σ k) + R) / (2 * R), ⟨?_, ?_⟩, ?_⟩
      · intro k; simp only [Pi.zero_apply]
        rw [le_div_iff₀ (by positivity)]; have := (abs_le.mp (hxbd (σ k))).1; linarith
      · intro k; simp only [Pi.one_apply]
        rw [div_le_one (by positivity)]; have := (abs_le.mp (hxbd (σ k))).2; linarith
      · ext i
        by_cases hij : i = j
        · rw [hφ]; simp only; rw [dif_pos hij, hij]; exact hxj.symm
        · rw [hφ]; simp only [dif_neg hij, Equiv.apply_symm_apply]; field_simp; ring

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:770. -/
theorem exists_lipschitz_cover_union {ι : Type*} [Fintype ι] (A B : Set (ι → ℝ))
    (h1 : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ A ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (h2 : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ B ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ (A ∪ B : Set (ι → ℝ)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  obtain ⟨m1, M1, φ1, hL1, hc1⟩ := h1
  obtain ⟨m2, M2, φ2, hL2, hc2⟩ := h2
  refine ⟨m1 + m2, max M1 M2, fun j ↦ Sum.elim φ1 φ2 (finSumFinEquiv.symm j), ?_, ?_⟩
  · intro j
    simp only
    rcases h : finSumFinEquiv.symm j with k | k
    · rw [Sum.elim_inl]; exact (hL1 k).weaken (le_max_left _ _)
    · rw [Sum.elim_inr]; exact (hL2 k).weaken (le_max_right _ _)
  · refine Set.union_subset ?_ ?_
    · refine hc1.trans (Set.iUnion_subset fun k ↦ ?_)
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inl k)) ?_
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, subset_refl]
    · refine hc2.trans (Set.iUnion_subset fun k ↦ ?_)
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inr k)) ?_
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, subset_refl]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:796. -/
theorem exists_lipschitz_cover_iUnion {ι : Type*} [Fintype ι] {γ : Type*} [Finite γ]
    (A : γ → Set (ι → ℝ))
    (h : ∀ g, ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ A g ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ (⋃ g, A g) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  classical
  have : Fintype γ := Fintype.ofFinite γ
  choose mf Mf φf hLf hcf using h
  set e := Fintype.equivFin (Σ g, Fin (mf g))
  set Ψ : (Σ g, Fin (mf g)) → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun p ↦ φf p.1 p.2 with hΨ
  refine ⟨Fintype.card (Σ g, Fin (mf g)), Finset.univ.sup Mf, fun j ↦ Ψ (e.symm j), ?_, ?_⟩
  · intro j
    exact (hLf (e.symm j).1 (e.symm j).2).weaken (Finset.le_sup (Finset.mem_univ _))
  · refine Set.iUnion_subset fun g ↦ (hcf g).trans (Set.iUnion_subset fun k ↦ ?_)
    refine Set.subset_iUnion_of_subset (e ⟨g, k⟩) ?_
    simp only [hΨ, Equiv.symm_apply_apply, subset_refl]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:819. -/
theorem frontier_signOrthant_subset {ι κ : Type*} [Finite κ] (g : κ → ι) (s : Finset κ) :
    frontier ({y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
      ⊆ ⋃ k : κ, {y : ι → ℝ | y (g k) = 0} := by
  set O : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} with hO
  set Os : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) < 0) ∧ (∀ k ∉ s, 0 < y (g k))} with hOs
  have hOclosed : IsClosed O := by
    simp only [hO, Set.setOf_and, Set.setOf_forall]
    exact (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦
        isClosed_le (continuous_apply (g k)) continuous_const).inter
      (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦
        isClosed_le continuous_const (continuous_apply (g k)))
  have hOsopen : IsOpen Os := by
    simp only [hOs, Set.setOf_and, Set.setOf_forall]
    exact (isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun _ ↦
        isOpen_lt (continuous_apply (g k)) continuous_const).inter
      (isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun _ ↦
        isOpen_lt continuous_const (continuous_apply (g k)))
  have hsub : Os ⊆ O := fun y hy ↦ ⟨fun k hk ↦ (hy.1 k hk).le, fun k hk ↦ (hy.2 k hk).le⟩
  intro y hy
  have hyO : y ∈ O := hOclosed.closure_eq ▸ frontier_subset_closure hy
  have hyni : y ∉ interior O := by
    rw [frontier_eq_closure_inter_closure] at hy
    rw [interior_eq_compl_closure_compl]; exact fun hh ↦ hh hy.2
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
  exact hyni (mem_interior.mpr ⟨Os, hsub, hOsopen,
    ⟨fun k hk ↦ lt_of_le_of_ne (hyO.1 k hk) (hcon k),
     fun k hk ↦ lt_of_le_of_ne (hyO.2 k hk) (Ne.symm (hcon k))⟩⟩)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:854. -/
theorem exists_frontier_cover_inter_orthant {ι : Type*} [Fintype ι] {κ : Type*} [Finite κ]
    (g : κ → ι) (s : Finset κ) (D₀ : Set (ι → ℝ)) (hbdd : Bornology.IsBounded D₀)
    (hcov : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
          ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  classical
  obtain ⟨R, hR0, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ closure D₀, ∀ i, |x i| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd.closure
    refine ⟨max R 0, le_max_right _ _, fun x hx i ↦ ?_⟩
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ max R 0 := le_max_of_le_left (hR x hx)
  set O : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))}
  have hsub : frontier (D₀ ∩ O)
      ⊆ frontier D₀ ∪ ⋃ k : κ, {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R} := by
    refine (frontier_inter_subset D₀ O).trans (Set.union_subset ?_ ?_)
    · exact Set.inter_subset_left.trans Set.subset_union_left
    · refine fun x hx ↦ Or.inr ?_
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (frontier_signOrthant_subset g s hx.2)
      exact Set.mem_iUnion.mpr ⟨k, hxk, hRbd x hx.1⟩
  obtain ⟨m, M, φ, hL, hc⟩ := exists_lipschitz_cover_union (frontier D₀)
    (⋃ k : κ, {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R}) hcov
    (exists_lipschitz_cover_iUnion (fun k ↦ {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R})
      (fun k ↦ by
        obtain ⟨M, φ, hL, hc⟩ := exists_lipschitz_cube_cover_hyperplane_slab (g k) hR0
        exact ⟨1, M, fun _ ↦ φ, fun _ ↦ hL, hc.trans (Set.subset_iUnion_of_subset 0 subset_rfl)⟩))
  exact ⟨m, M, φ, hL, hsub.trans hc⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:887. -/
theorem mem_span_int_basisFun_iff {ι : Type*} [Finite ι] (v : ι → ℝ) :
    v ∈ span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
  have : Fintype ι := Fintype.ofFinite ι
  simp only [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ v, Pi.basisFun_repr,
    Set.mem_range, eq_intCast, eq_comm]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:970. -/
theorem exists_card_cell_sub_mul_rpow_le_explicit {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) (D₀ : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D₀) (hmeas : MeasurableSet D₀)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {κ : Type*} [Finite κ] (g : κ → ι) (s : Finset κ) :
    ∃ C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩
            t • (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})) : ℝ)
          - (MeasureTheory.volume.real
              (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
              / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T
                : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|)
              * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  classical
  haveI : Fintype κ := Fintype.ofFinite κ
  set T' : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := (LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T
  set Ds : Set (ι → ℝ) :=
    D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))}
  have hDsbdd : Bornology.IsBounded Ds := hbdd.subset Set.inter_subset_left
  have hOclosed : IsClosed {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} := by
    classical
    rw [setOf_and]
    refine IsClosed.inter ?_ ?_
    · have h : {y : ι → ℝ | ∀ k ∈ s, y (g k) ≤ 0} = ⋂ k ∈ s, {y : ι → ℝ | y (g k) ≤ 0} := by
        ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ ↦ isClosed_le (continuous_apply (g k)) continuous_const)
    · have h : {y : ι → ℝ | ∀ k ∉ s, 0 ≤ y (g k)}
          = ⋂ k ∈ (sᶜ : Finset κ), {y : ι → ℝ | 0 ≤ y (g k)} := by ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ ↦ isClosed_le continuous_const (continuous_apply (g k)))
  have hDsmeas : MeasurableSet Ds := hmeas.inter hOclosed.measurableSet
  exact exists_card_coset_inter_smul_sub_volume_mul_rpow_le T' Ds hDsbdd hDsmeas
    (exists_frontier_cover_inter_orthant g s D₀ hbdd hlip)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1012. -/
theorem exists_card_cell_sub_mul_rpow_le {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) (D₀ : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D₀) (hmeas : MeasurableSet D₀)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {κ : Type*} [Finite κ] (g : κ → ι) (s : Finset κ) :
    ∃ leadC C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩
            t • (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})) : ℝ)
          - leadC * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  obtain ⟨C, hC⟩ := exists_card_cell_sub_mul_rpow_le_explicit T m hm D₀ hbdd hmeas hlip g s
  exact ⟨MeasureTheory.volume.real
    (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
    / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T
      : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|, C, hC⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1037. -/
theorem exists_int_coord_of_mem {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    {x : mixedSpace K} (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (i : index K) :
    ∃ n : ℤ, (T.symm ((mixedEmbedding.stdBasis K).equivFunL x)) i = (n : ℝ) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
  have hmem : Φ x ∈ T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := by
    rw [hT]; exact ⟨x, hx, rfl⟩
  obtain ⟨v, hv, hveq⟩ := hmem
  have hsymm : T.symm (Φ x) = v := by rw [← hveq, LinearEquiv.symm_apply_apply]
  rw [hsymm]
  exact (mem_span_int_basisFun_iff v).mp hv i

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1058. -/
theorem sub_mem_nsmul_of_coord_eq {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (J : (Ideal (𝓞 K))⁰) (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    {x₁ x₂ : mixedSpace K}
    (hx₁ : x₁ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (hx₂ : x₂ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (hcos : ∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₁)) i) : ZMod m)) =
      ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₂)) i) : ZMod m))) :
    x₁ - x₂ ∈
      (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  choose n₁ hn₁ using exists_int_coord_of_mem J T hT hx₁
  choose n₂ hn₂ using exists_int_coord_of_mem J T hT hx₂
  rw [← hΦ] at hn₁ hn₂
  have hround : ∀ (x : mixedSpace K) (n : index K → ℤ),
      (∀ i, (T.symm (Φ x)) i = (n i : ℝ)) →
        ∀ i, round ((T.symm (Φ x)) i) = n i := fun x n h i ↦ by
    rw [h i, round_intCast]
  have hdvd : ∀ i, (m : ℤ) ∣ (n₁ i - n₂ i) := fun i ↦ by
    have h := hcos i
    rw [hround x₁ n₁ hn₁ i, hround x₂ n₂ hn₂ i] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact h
  choose p hp using hdvd
  have hdiff : T.symm (Φ x₁) - T.symm (Φ x₂) = (m : ℝ) • (fun i ↦ (p i : ℝ)) := by
    funext i
    rw [Pi.sub_apply, Pi.smul_apply, hn₁ i, hn₂ i, smul_eq_mul]
    have hZ : (n₁ i - n₂ i : ℤ) = (m : ℤ) * p i := hp i
    have : (n₁ i : ℝ) - (n₂ i : ℝ) = (m : ℝ) * (p i : ℝ) := by exact_mod_cast hZ
    linarith
  have hpmem : (fun i ↦ (p i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) :=
    (mem_span_int_basisFun_iff _).mpr (fun i ↦ ⟨p i, rfl⟩)
  have hTp : T (fun i ↦ (p i : ℝ)) ∈ Φ '' (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
    rw [← hT]; exact ⟨_, hpmem, rfl⟩
  obtain ⟨z, hzmem, hzeq⟩ := hTp
  refine ⟨z, hzmem, ?_⟩
  have hkey : Φ (x₁ - x₂) = Φ ((m : ℝ) • z) := by
    rw [map_sub, map_smul]
    have h1 : Φ x₁ - Φ x₂ = T (T.symm (Φ x₁) - T.symm (Φ x₂)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [h1, hdiff, map_smul, hzeq]
  exact (Φ.injective hkey).symm

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1110. -/
theorem norm_zmod_eq_of_emb_sub_mem {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (J : (Ideal (𝓞 K))⁰) (x y : 𝓞 K)
    (hsub : mixedEmbedding K (x : K) - mixedEmbedding K (y : K) ∈
      (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))) :
    ((Algebra.norm ℤ x : ℤ) : ZMod m) = ((Algebra.norm ℤ y : ℤ) : ZMod m) := by
  obtain ⟨v, hv, hveq⟩ := hsub
  simp only at hveq
  rw [SetLike.mem_coe, mem_idealLattice] at hv
  obtain ⟨yK, hyK, hyeq⟩ := hv
  simp only [FractionalIdeal.coe_mk0] at hyK
  obtain ⟨w, _, hweq⟩ := hyK
  rw [Algebra.linearMap_apply] at hweq
  have hkey : mixedEmbedding K ((x - y : 𝓞 K) : K)
      = mixedEmbedding K (((m : 𝓞 K) * w : 𝓞 K) : K) := by
    push_cast
    rw [map_sub, ← hveq, ← hyeq, ← hweq, Nat.cast_smul_eq_nsmul, ← map_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  have hxy : x - y = (m : 𝓞 K) * w :=
    RingOfIntegers.coe_injective (K := K) ((mixedEmbedding_injective K) hkey)
  have hx : x = y + (m : 𝓞 K) * w := by linear_combination hxy
  rw [hx]
  exact natCast_algebraNorm_add_nsmul_mul m y w

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1135. -/
theorem mixedEmbedding_preimageOfMemIntegerSet_idealSetMap {K : Type*} [Field K]
    [NumberField K] (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    mixedEmbedding K ((preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : K) =
      (a : mixedSpace K) := by
  rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1146. -/
theorem residue_iff_signed_on_orthant {K : Type*} [Field K] [NumberField K]
    (m b : ℕ) (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    (s : Finset {w : InfinitePlace K // IsReal w})
    (hneg : ∀ w ∈ s, (a : mixedSpace K).1 w < 0)
    (hpos : ∀ w ∉ s, 0 < (a : mixedSpace K).1 w) :
    ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
      (((-1) ^ s.card * (Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : ℤ) :
        ℤ) : ZMod m) = (b : ZMod m) := by
  set gen : 𝓞 K := (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K)
  have hema : mixedEmbedding K (gen : K) = (a : mixedSpace K) :=
    mixedEmbedding_preimageOfMemIntegerSet_idealSetMap J a
  have hsign := natAbs_norm_eq_neg_one_pow_mul_norm gen s
    (fun w hw ↦ by rw [hema]; exact hneg w hw) (fun w hw ↦ by rw [hema]; exact hpos w hw)
  have hRes : intNorm (idealSetEquiv K J a).val = (Algebra.norm ℤ gen).natAbs := rfl
  have hcast : ((intNorm (idealSetEquiv K J a).val : ℕ) : ZMod m) =
      (((-1) ^ s.card * (Algebra.norm ℤ gen : ℤ) : ℤ) : ZMod m) := by
    rw [hRes, ← hsign, Int.cast_natCast]
  rw [hcast]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1171. -/
theorem mem_coset_iff_cos_eq {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (k : index K → ZMod m) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
    (mixedEmbedding.stdBasis K).equivFunL x ∈
        ((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ↔
      (∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x)) i) : ZMod m)) = k i) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  choose n hn using exists_int_coord_of_mem J T hT hx
  rw [← hΦ] at hn
  have hround : ∀ i, round ((T.symm (Φ x)) i) = n i := fun i ↦ by rw [hn i, round_intCast]
  simp only [hround, Set.mem_vadd_set, Set.mem_image, SetLike.mem_coe]
  have hgoal : (∀ i, ((n i : ZMod m)) = k i) ↔ (∀ i, (m : ℤ) ∣ (n i - (k i).val)) := by
    refine forall_congr' fun i ↦ ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  rw [hgoal]
  have hkey : ∀ p : index K → ℤ,
      (T ((fun i ↦ ((k i).val : ℝ)) + (m : ℝ) • (fun i ↦ (p i : ℝ))) = Φ x) ↔
        (∀ i, n i = (k i).val + (m : ℤ) * p i) := fun p ↦ by
    rw [← (LinearEquiv.eq_symm_apply T)]
    constructor
    · intro heq i
      have hc := congrFun heq i
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i] at hc
      have : (n i : ℝ) = ((k i).val + (m : ℤ) * p i : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro h
      funext i
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i]
      have := h i; push_cast [this]; ring
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, hweq⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add] at hweq
    rw [mem_span_int_basisFun_iff] at hv
    choose p hp using hv
    have hpp : v = (fun i ↦ (p i : ℝ)) := funext hp
    rw [hpp] at hweq
    exact fun i ↦ ⟨p i, by rw [(hkey p).mp hweq i]; ring⟩
  · intro h
    choose p hp using h
    refine ⟨(LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T (fun i ↦ (p i : ℝ)),
      ⟨_, (mem_span_int_basisFun_iff _).mpr (fun i ↦ ⟨p i, rfl⟩), rfl⟩, ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add]
    exact (hkey p).mpr fun i ↦ by have := hp i; omega

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1226. -/
theorem realComponent_ne_zero_of_mem_fundamentalCone {K : Type*} [Field K] [NumberField K]
    {x : mixedSpace K} (hx : x ∈ fundamentalCone K) (w : {w : InfinitePlace K // IsReal w}) :
    x.1 w ≠ 0 := fun h ↦ by
  have hp := fundamentalCone.normAtPlace_pos_of_mem hx w.1
  rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2] at hp
  simp [h] at hp

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1240. -/
theorem mem_smul_cell_iff_norm_le_and_filter_eq {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (s : Finset {w : InfinitePlace K // IsReal w}) {t : ℝ} (ht : 1 ≤ t)
    {x : mixedSpace K} (hx : x ∈ idealSet K J) :
    (mixedEmbedding.stdBasis K).equivFunL x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL ''
        (normLeOne K) ∩ {y : index K → ℝ |
          (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))}) ↔
      (mixedEmbedding.norm x ≤ t ^ Module.finrank ℚ K ∧
        Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K
  have hΦreal : ∀ (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}),
      Φ x (Sum.inl w) = x.1 w := fun x w ↦ by
    rw [hΦ, Module.Basis.equivFunL_apply, mixedEmbedding.stdBasis_apply_isReal]
  have hcone : {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d}
      = t • normLeOne K := cone_normLe_eq_smul_normLeOne ht
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos ht)
  have himg : Φ '' (t • normLeOne K) = t • (Φ '' normLeOne K) :=
    Set.image_smul_comm Φ t _ (fun b ↦ map_smul Φ t b)
  have hnz : ∀ x ∈ t • normLeOne K, ∀ w : {w : InfinitePlace K // IsReal w}, x.1 w ≠ 0 := by
    rintro _ ⟨z, hz, rfl⟩ w
    exact realComponent_ne_zero_of_mem_fundamentalCone (smul_mem_of_mem hz.1 ht0) w
  rw [Set.smul_set_inter₀ ht0, Set.mem_inter_iff, ← himg]
  constructor
  · rintro ⟨hmem, horth⟩
    rw [Set.mem_image] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    have hxcone : x ∈ t • normLeOne K := by rwa [Φ.injective hzeq] at hz
    have hnorm : x ∈ {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d} := by
      rw [hcone]; exact hxcone
    refine ⟨hnorm.2, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0] at horth
    obtain ⟨hneg, hpos⟩ := horth
    refine ⟨fun hlt ↦ ?_, fun hw ↦ ?_⟩
    · by_contra hws
      have h2 := hpos w hws
      rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
      nlinarith [h2, htinv, hlt]
    · have h2 := hneg w hw
      rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
      rcases lt_or_gt_of_ne (hnz x hxcone w) with h | h
      · exact h
      · nlinarith [h2, htinv, h]
  · rintro ⟨hnorm, horth⟩
    have hxcone : x ∈ t • normLeOne K := by rw [← hcone]; exact ⟨hx.1, hnorm⟩
    refine ⟨⟨x, hxcone, rfl⟩, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0]
    refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
      have hlt : x.1 w < 0 := by
        have : w ∈ Finset.univ.filter (fun w ↦ x.1 w < 0) := horth ▸ hw
        simpa using this
      nlinarith [hlt, htinv]
    · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
      have hxw : ¬ x.1 w < 0 := fun hlt ↦ hw (by
        have : w ∈ Finset.univ.filter (fun w ↦ x.1 w < 0) := by simpa using hlt
        rwa [horth] at this)
      nlinarith [not_lt.mp hxw, htinv]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1307. -/
theorem mem_idealSet_of_chart_mem_smul_cell {K : Type*} [Field K] [NumberField K]
    (I : (Ideal (𝓞 K))⁰) {t : ℝ} (ht0 : t ≠ 0) {Os : Set (index K → ℝ)}
    {y : index K → ℝ} {z : mixedSpace K}
    (hzlat : z ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I))
    (hzeq : (mixedEmbedding.stdBasis K).equivFunL z = y)
    (hregion : y ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) :
    z ∈ idealSet K I := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
  have himg : Φ '' (t • normLeOne K) = t • (Φ '' normLeOne K) :=
    Set.image_smul_comm Φ t _ (fun b ↦ map_smul Φ t b)
  obtain ⟨hmem, _⟩ := (by rwa [Set.smul_set_inter₀ ht0, Set.mem_inter_iff] at hregion :
    y ∈ t • (Φ '' normLeOne K) ∧ y ∈ t • Os)
  rw [← himg, Set.mem_image] at hmem
  obtain ⟨z', hz', hz'eq⟩ := hmem
  have hzn : z ∈ t • normLeOne K := by
    rw [show z = z' from Φ.injective (by rw [hz'eq, hzeq])]; exact hz'
  exact ⟨(by obtain ⟨z'', hz'', rfl⟩ := hzn; exact smul_mem_of_mem hz''.1 ht0), hzlat⟩

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1334. -/
theorem card_fibre_eq_card_cell {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
    {t : ℝ} (ht : 1 ≤ t) :
    Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = k}
    = Nat.card ↑(((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
        (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
  set d := Module.finrank ℚ K
  set f : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} → (index K → ℝ) :=
    fun a ↦ Φ (a.1 : mixedSpace K) with hf
  have hfinj : Function.Injective f := fun _ _ h ↦ Subtype.ext (Subtype.ext (Φ.injective h))
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  have hreg : ∀ x : mixedSpace K, x ∈ idealSet K J →
      (Φ x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os) ↔
        (mixedEmbedding.norm x ≤ t ^ d ∧
          Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s)) :=
    fun x hx ↦ mem_smul_cell_iff_norm_le_and_filter_eq J s ht hx
  have hsub : ((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
      (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
        (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))))
      ⊆ (Φ '' (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)) := by
    rw [← hT]
    rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add]
    rw [← map_add]
    refine ⟨_, ?_, rfl⟩
    refine add_mem ((mem_span_int_basisFun_iff _).mpr (fun i ↦ ⟨(k i).val, rfl⟩)) ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv _
  have hset : Set.range f =
      (((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
        (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) := by
    ext y
    simp only [hf, Set.mem_range, Subtype.exists, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hP, rfl⟩
      refine ⟨(mem_coset_iff_cos_eq m hm J T hT k ha.2).mpr (fun i ↦ congrFun hP.2.2 i), ?_⟩
      exact hreg a ha |>.mpr ⟨hP.1, hP.2.1⟩
    · rintro ⟨hcoset, hregion⟩
      obtain ⟨z, hzlat, hzeq⟩ := hsub hcoset
      have hzcone : z ∈ idealSet K J :=
        mem_idealSet_of_chart_mem_smul_cell J ht0 hzlat hzeq hregion
      refine ⟨z, hzcone, ⟨?_, ?_, ?_⟩, hzeq⟩
      · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).1
      · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).2
      · funext i
        exact (mem_coset_iff_cos_eq m hm J T hT k hzcone.2).mp (by rw [hzeq]; exact hcoset) i
  rw [← Nat.card_range_of_injective hfinj, hset]

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1408. -/
theorem residue_fibre_const_aux {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
    (a a' : idealSet K J)
    (horth : Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
      (a : mixedSpace K).1 w < 0) = s)
    (hcos : (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
      (a : mixedSpace K))) i) : ZMod m)) = k)
    (horth' : Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
      (a' : mixedSpace K).1 w < 0) = s)
    (hcos' : (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
      (a' : mixedSpace K))) i) : ZMod m)) = k) :
    (((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
      ((intNorm (idealSetEquiv K J a').val : ZMod m) = (b : ZMod m))) := by
  classical
  have hsign : ∀ c : idealSet K J,
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (c : mixedSpace K).1 w < 0) = s →
      (((intNorm (idealSetEquiv K J c).val : ZMod m) = (b : ZMod m)) ↔
        (((-1) ^ s.card *
          (Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J c) : 𝓞 K) : ℤ) : ℤ) :
          ZMod m) = (b : ZMod m)) := by
    intro c hc
    refine residue_iff_signed_on_orthant m b J c s (fun w hw ↦ ?_) (fun w hw ↦ ?_)
    · have : w ∈ Finset.univ.filter (fun w ↦ (c : mixedSpace K).1 w < 0) := hc ▸ hw
      simpa using this
    · have hcw : (c : mixedSpace K).1 w ≠ 0 :=
        realComponent_ne_zero_of_mem_fundamentalCone c.2.1 w
      have hge : ¬ (c : mixedSpace K).1 w < 0 := fun hlt ↦ hw (by
        have : w ∈ Finset.univ.filter (fun w ↦ (c : mixedSpace K).1 w < 0) := by simpa using hlt
        rwa [hc] at this)
      exact lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hcw)
  rw [hsign a horth, hsign a' horth']
  have hnormeq : ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : ℤ) :
        ZMod m) =
      ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a') : 𝓞 K) : ℤ) : ZMod m) := by
    refine norm_zmod_eq_of_emb_sub_mem m J _ _ ?_
    rw [mixedEmbedding_preimageOfMemIntegerSet_idealSetMap J a,
      mixedEmbedding_preimageOfMemIntegerSet_idealSetMap J a']
    exact sub_mem_nsmul_of_coord_eq m J T hT a.2.2 a'.2.2 (fun i ↦ by
      rw [congrFun hcos i, congrFun hcos' i])
  push_cast
  rw [hnormeq]

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1461. -/
theorem exists_card_residue_fibre_sub_mul_rpow_le_explicit {K : Type*} [Field K]
    [NumberField K] (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ)
          - (if (∃ a : idealSet K J,
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
            else 0) * t ^ Module.finrank ℚ K|
        ≤ C * t ^ (Module.finrank ℚ K - 1 : ℕ) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  have hcard : Fintype.card (index K) = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  have hconst : ∀ a a' : idealSet K J,
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ (a : mixedSpace K).1 w < 0)
        = s →
      (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k →
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ (a' : mixedSpace K).1 w < 0)
        = s →
      (fun i ↦ (round ((T.symm (Φ (a' : mixedSpace K))) i) : ZMod m)) = k →
      (((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
        ((intNorm (idealSetEquiv K J a').val : ZMod m) = (b : ZMod m))) :=
    fun a a' h1 h2 h3 h4 ↦ residue_fibre_const_aux m b J T hT s k a a' h1 h2 h3 h4
  by_cases hQ : ∃ a : idealSet K J,
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      ((fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k) ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))
  · obtain ⟨a₀, horth₀, hcos₀, hres₀⟩ := hQ
    obtain ⟨cellC, hcell⟩ := exists_card_cell_sub_mul_rpow_le_explicit T m hm
      (Φ '' (normLeOne K)) (Φ.lipschitz.isBounded_image (isBounded_normLeOne K))
      ((Φ.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (measurableSet_normLeOne K))
      hcov (Sum.inl : {w : InfinitePlace K // IsReal w} → index K) s
    refine ⟨cellC, fun t ht ↦ ?_⟩
    rw [if_pos ⟨a₀, horth₀, hcos₀, hres₀⟩]
    have hfibre : Nat.card {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k}
        = Nat.card {a : idealSet K J //
          mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
      constructor
      · rintro ⟨⟨hn, _⟩, ho, hc⟩; exact ⟨hn, ho, hc⟩
      · rintro ⟨hn, ho, hc⟩
        exact ⟨⟨hn, (hconst a a₀ ho hc horth₀ hcos₀).mpr hres₀⟩, ho, hc⟩
    rw [hfibre, card_fibre_eq_card_cell m hm J T hT s k ht]
    have hpow1 : t ^ Module.finrank ℚ K = t ^ Fintype.card (index K) := by rw [hcard]
    have hpow2 : t ^ (Module.finrank ℚ K - 1 : ℕ) = t ^ (Fintype.card (index K) - 1 : ℕ) := by
      rw [hcard]
    rw [hpow1, hpow2]
    exact hcell (T (fun i ↦ ((k i).val : ℝ))) t ht
  · refine ⟨0, fun t ht ↦ ?_⟩
    rw [if_neg hQ]
    have hempty : IsEmpty {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} :=
      ⟨fun a ↦ hQ ⟨a.1, a.2.2.1, a.2.2.2, a.2.1.2⟩⟩
    simp [Nat.card_of_isEmpty]

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1557. -/
theorem exists_card_residue_fibre_sub_mul_rpow_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ L C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ) - L * t ^ Module.finrank ℚ K|
        ≤ C * t ^ (Module.finrank ℚ K - 1 : ℕ) := by
  obtain ⟨C, hC⟩ := exists_card_residue_fibre_sub_mul_rpow_le_explicit m hm b J T hT hcov s k
  exact ⟨if (∃ a : idealSet K J,
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
    else 0, C, hC⟩

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1595. -/
theorem finite_idealSet_norm_le {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (s : ℝ) :
    Finite {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  classical
  have : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} :=
    (Ideal.finite_setOf_absNorm_le₀ ⌊s⌋₊).to_subtype
  refine Finite.of_injective (β := {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} ×
      torsion K) (fun a ↦ ⟨⟨(integerSetEquiv K (idealSetMap K J a.1)).1.1, ?_⟩,
    (integerSetEquiv K (idealSetMap K J a.1)).2⟩) ?_
  · have hnorm : Ideal.absNorm ((integerSetEquiv K (idealSetMap K J a.1)).1.1 : Ideal (𝓞 K))
        = intNorm (idealSetMap K J a.1) := by
      rw [integerSetEquiv_apply_fst, intNorm, Ideal.absNorm_span_singleton]
    rw [hnorm]
    refine Nat.le_floor ?_
    rw [intNorm_coe, idealSetMap_apply]
    exact a.2
  · intro a a' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    have : integerSetEquiv K (idealSetMap K J a.1) = integerSetEquiv K (idealSetMap K J a'.1) :=
      Prod.ext (Subtype.ext h.1) h.2
    have h2 : idealSetMap K J a.1 = idealSetMap K J a'.1 := (integerSetEquiv K).injective this
    exact Subtype.ext (Subtype.ext (by
      have := congrArg (Subtype.val) h2; simpa [idealSetMap_apply] using this))

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1623. -/
theorem card_idealSet_residue_eq_sum_cell {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (b : ℕ) (I₀ : (Ideal (𝓞 K))⁰)
    (Tc : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) (S : ℝ) :
    Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
        ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))}
      = ∑ p : Finset {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} ×
          (index K → ZMod m),
        Nat.card {a : idealSet K I₀ //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
            ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : NumberField.InfinitePlace K //
            NumberField.InfinitePlace.IsReal w} ↦ (a : mixedSpace K).1 w < 0) = p.1) ∧
          (fun i ↦ (round ((Tc.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = p.2} := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  let cls : {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
      ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} →
      Finset {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} ×
        (index K → ZMod m) :=
    fun a ↦ (Finset.univ.filter (fun w ↦ (a.1 : mixedSpace K).1 w < 0),
      fun i ↦ (round ((Tc.symm (Φ (a.1 : mixedSpace K))) i) : ZMod m))
  have hfinbase : Finite {a : idealSet K I₀ //
      mixedEmbedding.norm (a : mixedSpace K) ≤ S} :=
    finite_idealSet_norm_le I₀ _
  have : ∀ p : Finset {w : NumberField.InfinitePlace K //
      NumberField.InfinitePlace.IsReal w} × (index K → ZMod m),
      Finite {a : idealSet K I₀ //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
          ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : NumberField.InfinitePlace K //
          NumberField.InfinitePlace.IsReal w} ↦ (a : mixedSpace K).1 w < 0) = p.1) ∧
        (fun i ↦ (round ((Tc.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = p.2} := fun p ↦
    Finite.of_injective (fun a ↦ (⟨a.1, a.2.1.1⟩ : {a : idealSet K I₀ //
      mixedEmbedding.norm (a : mixedSpace K) ≤ S}))
      (fun x y h ↦ Subtype.ext (by simpa using h))
  rw [← Nat.card_sigma]
  refine Nat.card_congr ((Equiv.sigmaFiberEquiv cls).symm.trans (Equiv.sigmaCongrRight fun p ↦
    ?_))
  exact {
    toFun := fun a ↦ ⟨a.1.1, ⟨a.1.2, by
        have := a.2; simp only [cls, Prod.ext_iff] at this; exact ⟨this.1, this.2⟩⟩⟩
    invFun := fun a ↦ ⟨⟨a.1, a.2.1⟩, by simp only [cls, Prod.ext_iff]; exact ⟨a.2.2.1, a.2.2.2⟩⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

open scoped Classical in
/-- Planning source: ForMathlib/IdealCongruenceCount.lean:1674. -/
theorem card_residue_sum_bound_aux {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (b : ℕ) (I₀ : (Ideal (𝓞 K))⁰)
    (Tc : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) (S : ℝ) (hS : 1 ≤ S)
    (Lc Cc : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) → ℝ)
    (hcell : ∀ (p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m)) (tN : ℝ),
      1 ≤ tN →
      |(Nat.card {a : idealSet K I₀ //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ tN ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = p.1) ∧
          (fun i ↦ (round ((Tc.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = p.2} : ℝ) - Lc p * tN ^ Module.finrank ℚ K|
        ≤ Cc p * tN ^ (Module.finrank ℚ K - 1 : ℕ)) :
    |(Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
        ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} : ℝ)
        - (∑ p, Lc p) * S|
      ≤ (∑ p, Cc p) * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set tN : ℝ := S ^ ((d : ℝ)⁻¹) with htN
  have hs0 : (0 : ℝ) < S := lt_of_lt_of_le one_pos hS
  have htN1 : 1 ≤ tN := Real.one_le_rpow hS (by positivity)
  have htNd : tN ^ d = S := by
    rw [htN, ← Real.rpow_natCast (S ^ ((d : ℝ)⁻¹)) d, ← Real.rpow_mul hs0.le,
      inv_mul_cancel₀ hdne, Real.rpow_one]
  have htNd1 : tN ^ (d - 1 : ℕ) = S ^ (1 - (d : ℝ)⁻¹) := by
    have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hdpos]; simp
    rw [htN, ← Real.rpow_natCast (S ^ ((d : ℝ)⁻¹)) (d - 1), ← Real.rpow_mul hs0.le, hdcast]
    congr 1
    rw [inv_mul_eq_div, sub_div, div_self hdne, one_div]
  rw [card_idealSet_residue_eq_sum_cell m b I₀ Tc S, Nat.cast_sum]
  have hlead : (∑ p, Lc p) * S = ∑ p, Lc p * tN ^ d := by rw [← Finset.sum_mul, htNd]
  rw [hlead, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : (∑ p, Cc p) * S ^ (1 - (d : ℝ)⁻¹) = ∑ p, Cc p * tN ^ (d - 1 : ℕ) := by
    simp_rw [htNd1, Finset.sum_mul]
  rw [hbound]
  refine Finset.sum_le_sum (fun p _ ↦ ?_)
  rw [← htNd]
  exact hcell p tN htN1

end Cox.Chebotarev
