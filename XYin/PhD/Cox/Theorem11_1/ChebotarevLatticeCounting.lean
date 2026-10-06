/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Effective lattice counts
Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`.
-/
noncomputable section
open Submodule MeasureTheory Set BoxIntegral.unitPartition
open scoped NNReal Pointwise
namespace Cox.Chebotarev

/-- Planning source: ForMathlib/LatticePointCount.lean:59. -/
theorem ceil_natCast_mul_le_ceil_natCast_mul_add (n : ℕ) {a b r : ℝ} (h : a ≤ b + r) :
    (⌈(n : ℝ) * a⌉ : ℤ) ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ :=
  calc (⌈(n : ℝ) * a⌉ : ℤ)
      ≤ ⌈(n : ℝ) * b + (n : ℝ) * r⌉ :=
        Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    _ ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _

/-- Planning source: ForMathlib/LatticePointCount.lean:66. -/
theorem abs_sub_le_one_div_of_ceil_natCast_mul_eq {n : ℕ} (hn : 0 < (n : ℝ)) {a b : ℝ}
    (h : ⌈(n : ℝ) * a⌉ = ⌈(n : ℝ) * b⌉) : |a - b| ≤ 1 / n := by
  have hr : (⌈(n : ℝ) * a⌉ : ℝ) = ⌈(n : ℝ) * b⌉ := by exact_mod_cast h
  rw [show a - b = ((n : ℝ) * a - (n : ℝ) * b) / n by field_simp, abs_div, abs_of_pos hn,
    div_le_div_iff_of_pos_right hn, abs_le]
  constructor <;>
    nlinarith [Int.le_ceil ((n : ℝ) * a), Int.le_ceil ((n : ℝ) * b),
      Int.ceil_lt_add_one ((n : ℝ) * a), Int.ceil_lt_add_one ((n : ℝ) * b), hr]

/-- Planning source: ForMathlib/LatticePointCount.lean:79. -/
theorem setFinite_index_image_of_isBounded {ι : Type*} [Finite ι] (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ι → ℝ)
  set F : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ : ι ↦ Finset.Icc (⌈-((n : ℝ) * R)⌉ - 1) (⌈(n : ℝ) * R⌉ - 1) with hF
  refine Set.Finite.subset (Finset.finite_toSet F) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, index_apply]
  intro i
  have hxi : |x i| ≤ R := by
    have hd : dist (x i) ((0 : ι → ℝ) i) ≤ dist x 0 := dist_le_pi_dist x 0 i
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hd
    exact hd.trans (by simpa [Real.dist_eq] using hR hx)
  rcases abs_le.mp hxi with ⟨hlo, hhi⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact ⟨sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1,
    sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1⟩

/-- Planning source: ForMathlib/LatticePointCount.lean:101. -/
theorem ncard_index_image_le_of_diam_le {ι : Type*} [Fintype ι] (n : ℕ) [NeZero n]
    {T : Set (ι → ℝ)} {r : ℝ}
    (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) :
    (index n '' T).ncard ≤ (2 * ⌈(n : ℝ) * r⌉₊ + 1) ^ Fintype.card ι := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [image_empty, ncard_empty, zero_le]
  set K : ℕ := ⌈(n : ℝ) * r⌉₊ with hK
  set c : ι → ℤ := index n x₀ with hc
  set F : Finset (ι → ℤ) := Fintype.piFinset fun i ↦ Finset.Icc (c i - K) (c i + K) with hF
  have hsub : index n '' T ⊆ ↑F := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hdx : |x i - x₀ i| ≤ r := by
      have h1 : dist (x i) (x₀ i) ≤ dist x x₀ := dist_le_pi_dist x x₀ i
      rw [Real.dist_eq] at h1
      exact h1.trans ((Metric.dist_le_diam_of_mem hbdd hx hx₀).trans hdiam)
    rcases abs_le.mp hdx with ⟨hlo, hhi⟩
    have hKeq : (K : ℤ) = ⌈(n : ℝ) * r⌉ := hK ▸ Int.natCast_ceil_eq_ceil (by positivity)
    have hub :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x i) (b := x₀ i) (r := r) (by linarith)
    have hlb :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x₀ i) (b := x i) (r := r) (by linarith)
    simp only [index_apply, hc]
    constructor <;> omega
  refine (Set.ncard_le_ncard hsub F.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset, hF, Fintype.card_piFinset]
  have hcard : ∀ i, (Finset.Icc (c i - K) (c i + K)).card = 2 * K + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ ↦ hcard i, Finset.prod_const, Finset.card_univ]

/-- Planning source: ForMathlib/LatticePointCount.lean:137. -/
theorem ncard_index_image_chart_le {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] {M : ℝ≥0}
    {φ : (κ → ℝ) → (ι → ℝ)}
    (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) :
    (index n '' (φ '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card κ) := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  set q : (κ → ℝ) → (κ → ℤ) :=
    fun y k ↦ ⌈(n : ℝ) * y k⌉ with hq
  set T : Finset (κ → ℤ) :=
    Finset.Icc (0 : κ → ℤ) (fun _ ↦ (n : ℤ)) with hT
  have hdiam : ∀ v : κ → ℤ,
      Metric.diam (Set.Icc 0 1 ∩ q ⁻¹' {v}) ≤ 1 / n := by
    intro v
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' ↦ ?_
    rw [dist_pi_le_iff (by positivity)]
    intro k
    have hce : ⌈(n : ℝ) * y k⌉ = ⌈(n : ℝ) * y' k⌉ :=
      (congrFun hy.2 k).trans (congrFun hy'.2 k).symm
    rw [Real.dist_eq]
    exact abs_sub_le_one_div_of_ceil_natCast_mul_eq hn0 hce
  have hcover : index n '' (φ '' Set.Icc 0 1) ⊆
      ⋃ v ∈ T, index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyT : q y ∈ T := by
      rw [hT, Finset.mem_Icc]
      refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
      · simp only [hq, Pi.zero_apply]
        rw [Int.le_ceil_iff]
        push_cast
        linarith [mul_nonneg hn0.le (hy.1 k)]
      · simp only [hq]
        rw [Int.ceil_le]
        have hyk : y k ≤ 1 := hy.2 k
        push_cast
        nlinarith [hn0]
    exact Set.mem_biUnion hyT ⟨φ y, ⟨y, ⟨hy, rfl⟩, rfl⟩, rfl⟩
  have hpiece : ∀ v : κ → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).ncard
        ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι := by
    intro v
    have hbddφ : Bornology.IsBounded (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) :=
      hφ.isBounded_image ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left)
    have hdimg : Metric.diam (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) ≤ (M : ℝ) * (1 / n) :=
      (hφ.diam_image_le _ ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left)).trans
        (mul_le_mul_of_nonneg_left (hdiam v) (by positivity))
    refine (ncard_index_image_le_of_diam_le n (by positivity) hdimg hbddφ).trans ?_
    rw [show (n : ℝ) * ((M : ℝ) * (1 / n)) = (M : ℝ) by field_simp]
  have hfin : ∀ v : κ → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).Finite :=
    fun v ↦ setFinite_index_image_of_isBounded n
      (hφ.isBounded_image ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left))
  refine (Set.ncard_le_ncard hcover (T.finite_toSet.biUnion fun v _ ↦ hfin v)).trans ?_
  refine (Finset.set_ncard_biUnion_le T _).trans ?_
  refine (Finset.sum_le_sum fun v _ ↦ hpiece v).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardT : T.card = (n + 1) ^ (Fintype.card κ) := by
    rw [hT, Pi.card_Icc]
    simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_natCast_add_one, Finset.prod_const,
      Finset.card_univ]
  rw [hcardT, Nat.cast_id]

/-- Planning source: ForMathlib/LatticePointCount.lean:202. -/
theorem ncard_index_image_frontier_le {ι : Type*} [Fintype ι] {t : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0}
    {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)}
    (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : t ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (index n '' t).ncard
      ≤ (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1))
          * n ^ (Fintype.card ι - 1) := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hbddφ : ∀ j, Bornology.IsBounded (φ j '' Set.Icc 0 1) := fun j ↦
    (hφ j).isBounded_image (Metric.isBounded_Icc 0 1)
  have hfin : ∀ j : Fin m, (index n '' (φ j '' Set.Icc 0 1)).Finite := fun j ↦
    setFinite_index_image_of_isBounded n (hbddφ j)
  have hsub : index n '' t ⊆ ⋃ j, index n '' (φ j '' Set.Icc 0 1) := by
    rw [← Set.image_iUnion]
    exact Set.image_mono hcov
  refine (Set.ncard_le_ncard hsub (Set.finite_iUnion hfin)).trans ?_
  refine (Set.ncard_iUnion_le_of_fintype _).trans ?_
  refine (Finset.sum_le_sum fun j _ ↦ ncard_index_image_chart_le (hφ j) hn).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (n + 1) ^ (Fintype.card ι - 1) ≤
      2 ^ (Fintype.card ι - 1) * n ^ (Fintype.card ι - 1) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) _
  calc
    (m : ℕ) * ((2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1))
      ≤ m * ((2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι
          * (2 ^ (Fintype.card ι - 1) * n ^ (Fintype.card ι - 1))) := by gcongr
    _ = m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1)
          * n ^ (Fintype.card ι - 1) := by ring

/-- Planning source: ForMathlib/LatticePointCount.lean:234. -/
theorem index_mem_image_frontier_of_box_meet_not_subset {ι : Type*} {n : ℕ} [NeZero n]
    {s : Set (ι → ℝ)} {ν : ι → ℤ} (hmeet : ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty)
    (hnsub : ¬ (box n ν : Set (ι → ℝ)) ⊆ s) : ν ∈ index n '' frontier s := by
  have hconn : IsPreconnected (box n ν : Set (ι → ℝ)) := by
    rw [BoxIntegral.Box.coe_eq_pi]
    exact (convex_pi fun _ _ ↦ convex_Ioc _ _).isPreconnected
  obtain ⟨xc, hxcb, hxcs⟩ : ((box n ν : Set (ι → ℝ)) ∩ sᶜ).Nonempty := by
    rw [Set.not_subset] at hnsub
    exact hnsub.imp fun _ ⟨hx, hxs⟩ ↦ ⟨hx, hxs⟩
  by_contra hcon
  have hcon' : (box n ν : Set (ι → ℝ)) ∩ frontier s = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxb, hxf⟩
    exact hcon ⟨x, hxf, mem_box_iff_index.mp hxb⟩
  have hsplit : (box n ν : Set (ι → ℝ)) ⊆ interior s ∪ (closure s)ᶜ := by
    intro x hx
    by_contra hxc
    rw [Set.mem_union, not_or, Set.notMem_compl_iff] at hxc
    exact (Set.eq_empty_iff_forall_notMem.mp hcon' x) ⟨hx, hxc.2, hxc.1⟩
  rcases hconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr (interior_subset.trans subset_closure)) hsplit
    with hsub | hsub
  · exact hxcs (interior_subset (hsub hxcb))
  · obtain ⟨x, hxb, hxs⟩ := hmeet
    exact (hsub hxb) (subset_closure hxs)

/-- Planning source: ForMathlib/LatticePointCount.lean:260. -/
theorem measureReal_biUnion_box {ι : Type*} [Fintype ι] (n : ℕ) [NeZero n] (t : Finset (ι → ℤ)) :
    volume.real (⋃ ν ∈ t, (box n ν : Set (ι → ℝ))) = t.card / (n : ℝ) ^ Fintype.card ι := by
  have hvol_box : ∀ ν : ι → ℤ,
      volume.real (box n ν : Set (ι → ℝ)) = 1 / (n : ℝ) ^ Fintype.card ι := by
    intro ν
    rw [measureReal_def, volume_box]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [measureReal_biUnion_finset (fun ν _ ν' _ h ↦ disjoint.mp h)
    (fun ν _ ↦ (box n ν).measurableSet_coe) (fun ν _ ↦ (box n ν).isBounded.measure_lt_top.ne)]
  simp_rw [hvol_box]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Planning source: ForMathlib/LatticePointCount.lean:276. -/
theorem abs_card_inter_sub_volume_mul_pow_le {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) :
    |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
        - volume.real s * (n : ℝ) ^ Fintype.card ι|
      ≤ (index n '' frontier s).ncard := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  have hvs : volume s ≠ ⊤ := hbdd.measure_lt_top.ne
  set Inside : Set (ι → ℤ) := {ν | (box n ν : Set (ι → ℝ)) ⊆ s}
  set Meet : Set (ι → ℤ) := {ν | ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty}
  set Bd : Set (ι → ℤ) := index n '' frontier s
  have hInsideFin : Inside.Finite := setFinite_index n hmeas.nullMeasurableSet hvs
  have hBdFin : Bd.Finite :=
    setFinite_index_image_of_isBounded n (hbdd.closure.subset frontier_subset_closure)
  have hMeetSub : Meet ⊆ index n '' s := by
    rintro ν ⟨x, hxb, hxs⟩
    exact ⟨x, hxs, mem_box_iff_index.mp hxb⟩
  have hMeetFin : Meet.Finite :=
    (setFinite_index_image_of_isBounded n hbdd).subset hMeetSub
  set Tag : Set (ι → ℤ) := {ν | tag n ν ∈ s} with hTag
  have himg : index n '' (s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag := by
    ext ν
    simp only [hTag, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hxs, hxL⟩, rfl⟩
      rwa [tag_index_eq_self_of_mem_smul_span n hxL]
    · intro hν
      exact ⟨tag n ν, ⟨hν, tag_mem_smul_span n ν⟩, index_tag n ν⟩
  have hNeq : Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag.ncard := by
    rw [Nat.card_coe_set_eq, ← himg]
    refine (Set.InjOn.ncard_image ?_).symm
    intro x hx y hy h
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 h
  have hIT : Inside ⊆ Tag := fun ν hν ↦ hν (tag_mem n ν)
  have hTM : Tag ⊆ Meet := fun ν hν ↦ ⟨tag n ν, tag_mem n ν, hν⟩
  have hMIB : Meet ⊆ Inside ∪ Bd := by
    intro ν hν
    by_cases hsub : (box n ν : Set (ι → ℝ)) ⊆ s
    · exact Or.inl hsub
    · exact Or.inr (index_mem_image_frontier_of_box_meet_not_subset hν hsub)
  have hcard_IT : Inside.ncard ≤ Tag.ncard :=
    Set.ncard_le_ncard hIT (hMeetFin.subset hTM)
  have hcard_TM : Tag.ncard ≤ Meet.ncard := Set.ncard_le_ncard hTM hMeetFin
  have hcard_MIB : Meet.ncard ≤ Inside.ncard + Bd.ncard :=
    (Set.ncard_le_ncard hMIB (hInsideFin.union hBdFin)).trans (Set.ncard_union_le _ _)
  set V : ℝ := volume.real s * (n : ℝ) ^ Fintype.card ι with hV
  have hnpow : (0 : ℝ) < (n : ℝ) ^ Fintype.card ι := by positivity
  have hcardI : (hInsideFin.toFinset).card = Inside.ncard :=
    (Set.ncard_eq_toFinset_card _ hInsideFin).symm
  have hcardM : (hMeetFin.toFinset).card = Meet.ncard :=
    (Set.ncard_eq_toFinset_card _ hMeetFin).symm
  have hvol_lower : (Inside.ncard : ℝ) ≤ V := by
    have hsub : (⋃ ν ∈ hInsideFin.toFinset, (box n ν : Set (ι → ℝ))) ⊆ s :=
      Set.iUnion₂_subset fun ν hν ↦ hInsideFin.mem_toFinset.mp hν
    have hle := measureReal_mono hsub hvs
    rw [measureReal_biUnion_box n hInsideFin.toFinset, hcardI, div_le_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hvol_upper : V ≤ (Meet.ncard : ℝ) := by
    have hsub : s ⊆ ⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ)) := by
      intro x hxs
      refine Set.mem_iUnion₂.mpr ⟨index n x, hMeetFin.mem_toFinset.mpr ?_,
        mem_box_iff_index.mpr rfl⟩
      exact ⟨x, mem_box_iff_index.mpr rfl, hxs⟩
    have hfinU : volume (⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ))) ≠ ⊤ :=
      (measure_biUnion_finset_le _ _).trans_lt (by
        simp only [volume_box]
        exact ENNReal.sum_lt_top.mpr fun _ _ ↦ by finiteness) |>.ne
    have hle := measureReal_mono hsub hfinU
    rw [measureReal_biUnion_box n hMeetFin.toFinset, hcardM, le_div_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hITr : (Inside.ncard : ℝ) ≤ (Tag.ncard : ℝ) := by exact_mod_cast hcard_IT
  have hMIBr : (Meet.ncard : ℝ) ≤ (Inside.ncard : ℝ) + (Bd.ncard : ℝ) := by
    exact_mod_cast hcard_MIB
  have hTMr : (Tag.ncard : ℝ) ≤ (Meet.ncard : ℝ) := by exact_mod_cast hcard_TM
  rw [hNeq, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Planning source: ForMathlib/LatticePointCount.lean:365. -/
theorem exists_card_inter_smul_lattice_sub_volume_mul_pow_le
    {ι : Type*} [Fintype ι] (s : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
          - volume.real s * (n : ℝ) ^ Fintype.card ι|
        ≤ C * (n : ℝ) ^ (Fintype.card ι - 1) := by
  obtain ⟨m, M, φ, hφ, hcov⟩ := hlip
  refine ⟨(m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1) : ℕ),
    fun n hn ↦ ?_⟩
  refine (abs_card_inter_sub_volume_mul_pow_le hbdd hmeas hn).trans ?_
  refine (Nat.cast_le.mpr (ncard_index_image_frontier_le hφ hcov hn)).trans ?_
  exact le_of_eq (by push_cast; ring)

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:83. -/
theorem isBounded_image_smul_add {ι : Type*} [Fintype ι] {δ : Type*} [Fintype δ] {M : ℝ≥0}
    {φ : (δ → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) (c : ℝ) (v : ι → ℝ)
    {A : Set (δ → ℝ)} (hA : Bornology.IsBounded A) :
    Bornology.IsBounded ((fun y ↦ v + c • φ y) '' A) := by
  have hb : Bornology.IsBounded (φ '' A) := hφ.isBounded_image hA
  have heq : (fun y ↦ v + c • φ y) '' A = v +ᵥ (c • (φ '' A)) := by
    ext z
    simp only [Set.mem_image, Set.mem_vadd_set, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨c • φ y, ⟨φ y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨u, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  rw [heq]
  exact (hb.smul₀ c).vadd v

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:97. -/
theorem diam_ceil_fibre_le {d : ℕ} (N : ℕ) (hN0 : (0 : ℝ) < N) (w : Fin d → ℤ) :
    Metric.diam (Set.Icc (0 : Fin d → ℝ) 1 ∩ (fun y k ↦ ⌈(N : ℝ) * y k⌉) ⁻¹' {w}) ≤ 1 / N := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' ↦ ?_
  rw [dist_pi_le_iff (by positivity)]
  intro k
  have hyv : (⌈(N : ℝ) * y k⌉ : ℤ) = w k := congrFun hy.2 k
  have hyv' : (⌈(N : ℝ) * y' k⌉ : ℤ) = w k := congrFun hy'.2 k
  have hce : ⌈(N : ℝ) * y k⌉ = ⌈(N : ℝ) * y' k⌉ := hyv.trans hyv'.symm
  have h1 : (⌈(N : ℝ) * y k⌉ : ℝ) - 1 < (N : ℝ) * y k ∧ (N : ℝ) * y k ≤ ⌈(N : ℝ) * y k⌉ :=
    Int.ceil_eq_iff.mp rfl
  have h2 : (⌈(N : ℝ) * y' k⌉ : ℝ) - 1 < (N : ℝ) * y' k ∧ (N : ℝ) * y' k ≤ ⌈(N : ℝ) * y' k⌉ :=
    Int.ceil_eq_iff.mp rfl
  rw [hce] at h1
  have habs : |(N : ℝ) * y k - (N : ℝ) * y' k| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  rw [Real.dist_eq, show y k - y' k = ((N : ℝ) * y k - (N : ℝ) * y' k) / N by
      field_simp, abs_div, abs_of_pos hN0]
  rw [div_le_div_iff_of_pos_right hN0]
  exact habs

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:125. -/
theorem ncard_index1_image_smul_chart_le {ι : Type*} [Fintype ι] {M : ℝ≥0}
    {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ)
    {c : ℝ} (hc : 1 ≤ c) (v : ι → ℝ) :
    (index 1 '' ((fun y ↦ v + c • φ y) '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (⌈c⌉₊ + 1) ^ (Fintype.card ι - 1) := by
  classical
  set N : ℕ := ⌈c⌉₊ with hN
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr hcpos
  have hNne : NeZero N := ⟨Nat.one_le_iff_ne_zero.mp hN1⟩
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne.out
  have hcN : c ≤ (N : ℝ) := Nat.le_ceil c
  set ψ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) := fun y ↦ v + c • φ y with hψ
  have hψbdd : ∀ A : Set (Fin (Fintype.card ι - 1) → ℝ), Bornology.IsBounded A →
      Bornology.IsBounded (ψ '' A) := fun A hA ↦ isBounded_image_smul_add hφ c v hA
  set q : (Fin (Fintype.card ι - 1) → ℝ) → (Fin (Fintype.card ι - 1) → ℤ) :=
    fun y k ↦ ⌈(N : ℝ) * y k⌉ with hq
  set T : Finset (Fin (Fintype.card ι - 1) → ℤ) :=
    Finset.Icc (0 : Fin (Fintype.card ι - 1) → ℤ) (fun _ ↦ (N : ℤ)) with hT
  have hdiam : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      Metric.diam (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}) ≤ 1 / N :=
    fun w ↦ diam_ceil_fibre_le N hN0 w
  have hcover : index 1 '' (ψ '' Set.Icc 0 1) ⊆
      ⋃ w ∈ T, index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w})) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyT : q y ∈ T := by
      rw [hT, Finset.mem_Icc]
      refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
      · simp only [hq, Pi.zero_apply]
        rw [Int.le_ceil_iff]
        have h0 : (0 : ℝ) ≤ (N : ℝ) * y k := mul_nonneg hN0.le (hy.1 k)
        push_cast
        linarith
      · simp only [hq]
        rw [Int.ceil_le]
        have hyk : y k ≤ 1 := (hy.2 k)
        push_cast
        nlinarith [hN0]
    exact Set.mem_biUnion hyT ⟨ψ y, ⟨y, ⟨hy, rfl⟩, rfl⟩, rfl⟩
  have hpiece : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      (index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}))).ncard
        ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι := by
    intro w
    set S : Set (Fin (Fintype.card ι - 1) → ℝ) :=
      Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w} with hS
    have hSbdd : Bornology.IsBounded S :=
      (Metric.isBounded_Icc 0 1).subset Set.inter_subset_left
    have hbddφ : Bornology.IsBounded (ψ '' S) := hψbdd S hSbdd
    have hdimg : Metric.diam (ψ '' S) ≤ (M : ℝ) := by
      refine Metric.diam_le_of_forall_dist_le M.coe_nonneg ?_
      rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      have hdd : dist (ψ y) (ψ y') = |c| * dist (φ y) (φ y') := by
        simp only [hψ, dist_add_left, dist_smul₀, Real.norm_eq_abs]
      have hφd : dist (φ y) (φ y') ≤ (M : ℝ) * (1 / N) := by
        refine (hφ.dist_le_mul y y').trans ?_
        refine mul_le_mul_of_nonneg_left ?_ M.coe_nonneg
        exact (Metric.dist_le_diam_of_mem hSbdd hy hy').trans (hdiam w)
      rw [hdd, abs_of_pos hcpos]
      have hfin : c * ((M : ℝ) * (1 / N)) ≤ (M : ℝ) := by
        rw [mul_one_div, mul_div_assoc', div_le_iff₀ hN0]
        nlinarith [hcN, M.coe_nonneg]
      exact le_trans (mul_le_mul_of_nonneg_left hφd hcpos.le) hfin
    refine (ncard_index_image_le_of_diam_le 1 M.coe_nonneg ?_ hbddφ).trans ?_
    · simpa using hdimg
    · simp
  have hfin : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      (index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}))).Finite :=
    fun w ↦ setFinite_index_image_of_isBounded 1
      (hψbdd _ ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left))
  refine (Set.ncard_le_ncard hcover (T.finite_toSet.biUnion fun w _ ↦ hfin w)).trans ?_
  refine (Finset.set_ncard_biUnion_le T _).trans ?_
  refine (Finset.sum_le_sum fun w _ ↦ hpiece w).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardT : T.card = (N + 1) ^ (Fintype.card ι - 1) := by
    rw [hT, Pi.card_Icc]
    simp only [Pi.zero_apply]
    have hk : ∀ k : Fin (Fintype.card ι - 1),
        (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
      intro k
      rw [Int.card_Icc]
      simp
    rw [Finset.prod_congr rfl fun k _ ↦ hk k, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hcardT, Nat.cast_id]

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:220. -/
theorem abs_cardR_translate_sub_volume_le {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {m : ℕ} {M : ℝ≥0}
    {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : ∀ j, LipschitzWith M (φ j))
    (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) (w : ι → ℝ) {c : ℝ} (hc : 1 ≤ c) :
    |(Nat.card ↑(s ∩ c⁻¹ •
        (w +ᵥ ((span ℤ (Set.range (Pi.basisFun ℝ ι))) : Set (ι → ℝ)))) : ℝ) -
      volume.real s * c ^ Fintype.card ι|
      ≤ (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1) : ℕ)
          * c ^ (Fintype.card ι - 1) := by
  classical
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hc0 : c ≠ 0 := hcpos.ne'
  set Λ : Submodule ℤ (ι → ℝ) := span ℤ (Set.range (Pi.basisFun ℝ ι))
  set R : Set (ι → ℝ) := (-w) +ᵥ (c • s) with hR
  have hcount : Nat.card ↑(s ∩ c⁻¹ • (w +ᵥ (Λ : Set (ι → ℝ)))) = Nat.card ↑(R ∩ Λ) := by
    have hbij1 : ↑(s ∩ c⁻¹ • (w +ᵥ (Λ : Set (ι → ℝ)))) ≃ ↑(c • s ∩ (w +ᵥ (Λ : Set (ι → ℝ)))) :=
      Equiv.subtypeEquiv (Equiv.smulRight hc0) (fun x ↦ by
        simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc0,
          ← Set.mem_inv_smul_set_iff₀ hc0])
    rw [Nat.card_congr hbij1]
    have heq : (-w) +ᵥ ((c • s) ∩ (w +ᵥ (Λ : Set (ι → ℝ)))) = R ∩ Λ := by
      rw [Set.vadd_set_inter, hR]
      congr 1
      rw [vadd_vadd]
      simp
    rw [← heq]
    exact (Nat.card_image_of_injective (fun a b h ↦ by simpa using h) _).symm
  rw [hcount]
  have hRbdd : Bornology.IsBounded R := (hbdd.smul₀ c).vadd (-w)
  have hRmeas : MeasurableSet R := (hmeas.const_smul_of_ne_zero hc0).const_vadd (-w)
  have hbridge := abs_card_inter_sub_volume_mul_pow_le hRbdd hRmeas (n := 1) le_rfl
  rw [Nat.cast_one, inv_one, one_smul, one_pow, mul_one] at hbridge
  have hvolR : volume.real R = c ^ Fintype.card ι * volume.real s := by
    rw [hR, Measure.real, measure_vadd, ← Measure.real,
      show volume.real (c • s) = |c| ^ (Fintype.card ι) * volume.real s by
        rw [Measure.real, Measure.real, MeasureTheory.Measure.addHaar_smul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), abs_pow, Module.finrank_pi],
      abs_of_pos hcpos]
  rw [hvolR] at hbridge
  have hchart_eq : ∀ j, (-w) +ᵥ (c • (φ j '' Set.Icc 0 1))
      = (fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1 := by
    intro j
    ext z
    simp only [Set.mem_vadd_set, Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨u, ⟨v, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩; exact ⟨y, hy, by simp [vadd_eq_add]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c • φ j y, ⟨φ j y, ⟨y, hy, rfl⟩, rfl⟩, by simp [vadd_eq_add]⟩
  have hfrontR : frontier R ⊆ ⋃ j, (fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1 := by
    have hcfr : c • frontier s = frontier (c • s) := by
      have := (Homeomorph.smulOfNeZero c hc0).image_frontier s
      simpa using this
    have hfr : frontier R = (-w) +ᵥ (c • frontier s) := by
      have h1 : frontier R = (Homeomorph.addLeft (-w)) '' frontier (c • s) :=
        ((Homeomorph.addLeft (-w)).image_frontier (c • s)).symm
      rw [h1, ← hcfr]
      rfl
    rw [hfr]
    refine (Set.vadd_set_mono (Set.smul_set_mono hcov)).trans ?_
    rw [Set.smul_set_iUnion, Set.vadd_set_iUnion]
    exact Set.iUnion_mono fun j ↦ (hchart_eq j).le
  have hbdcell : (index 1 '' frontier R).ncard ≤
      (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι) * (⌈c⌉₊ + 1) ^ (Fintype.card ι - 1) := by
    have hfin : ∀ j : Fin m, (index 1 '' ((fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1)).Finite :=
      fun j ↦ setFinite_index_image_of_isBounded 1
        (isBounded_image_smul_add (hφ j) c (-w) (Metric.isBounded_Icc 0 1))
    have hsub : index 1 '' frontier R ⊆
        ⋃ j, index 1 '' ((fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1) := by
      rw [← Set.image_iUnion]
      exact Set.image_mono hfrontR
    refine (Set.ncard_le_ncard hsub (Set.finite_iUnion hfin)).trans ?_
    refine (Set.ncard_iUnion_le_of_fintype _).trans ?_
    refine (Finset.sum_le_sum fun j _ ↦ ncard_index1_image_smul_chart_le (hφ j) hc (-w)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    rfl
  rw [mul_comm (c ^ Fintype.card ι) (volume.real s)] at hbridge
  refine hbridge.trans ((Nat.cast_le.mpr hbdcell).trans ?_)
  push_cast
  have hpow : ((⌈c⌉₊ : ℝ) + 1) ^ (Fintype.card ι - 1) ≤
      3 ^ (Fintype.card ι - 1) * c ^ (Fintype.card ι - 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have h1 : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hcpos.le
    nlinarith [hc]
  calc (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * ((⌈c⌉₊ : ℝ) + 1) ^ (Fintype.card ι - 1)
      ≤ (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι
          * (3 ^ (Fintype.card ι - 1) * c ^ (Fintype.card ι - 1)) := by
        gcongr
    _ = (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1)
          * c ^ (Fintype.card ι - 1) := by ring

/-- Planning source: ForMathlib/IdealCongruenceCount.lean:318. -/
theorem exists_card_coset_inter_smul_sub_volume_mul_rpow_le
    {ι : Type*} [Fintype ι] (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (D : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D) (hmeas : MeasurableSet D)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩ t • D) : ℝ)
          - MeasureTheory.volume.real D / |LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|
            * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  classical
  obtain ⟨m, M, φ, hφ, hcov⟩ := hlip
  set D' : Set (ι → ℝ) := T.symm '' D with hD'
  set Ts : (ι → ℝ) →L[ℝ] (ι → ℝ) := (T.symm.toContinuousLinearEquiv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    with hTs
  have hTslip : LipschitzWith ‖Ts‖₊ (T.symm : (ι → ℝ) → (ι → ℝ)) := by
    simpa [hTs] using Ts.lipschitz
  have hD'bdd : Bornology.IsBounded D' := hTslip.isBounded_image hbdd
  have hD'meas : MeasurableSet D' :=
    (T.symm.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr hmeas
  set M' : ℝ≥0 := ‖Ts‖₊ * M
  set φ' : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) := fun j ↦ T.symm ∘ φ j with hφ'
  have hφ'lip : ∀ j, LipschitzWith M' (φ' j) := fun j ↦ hTslip.comp (hφ j)
  have hcov' : frontier D' ⊆ ⋃ j, φ' j '' Set.Icc 0 1 := by
    have hfr : frontier D' = T.symm '' frontier D := by
      have h := (T.symm.toContinuousLinearEquiv.toHomeomorph).image_frontier D
      simpa [hD'] using h.symm
    rw [hfr]
    refine (Set.image_mono hcov).trans ?_
    rw [Set.image_iUnion]
    refine Set.iUnion_mono fun j ↦ ?_
    rw [Set.image_image]
    exact le_rfl
  have hvolD' : MeasureTheory.volume.real D' =
      MeasureTheory.volume.real D / |LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| := by
    have hcoe : (⇑T.symm : (ι → ℝ) → (ι → ℝ)) = ⇑(T.symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := rfl
    rw [hD', MeasureTheory.Measure.real, MeasureTheory.Measure.real, hcoe,
      MeasureTheory.Measure.addHaar_image_linearMap,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    have hdet : LinearMap.det (T.symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
        (LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))⁻¹ := by
      rw [← LinearEquiv.coe_det, ← LinearEquiv.coe_det, LinearEquiv.det_symm]
      simp [Units.val_inv_eq_inv_val]
    rw [hdet, abs_inv, div_eq_mul_inv]
    ring
  refine ⟨(m * (2 * ⌈(M' : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1) : ℕ), ?_⟩
  intro ξ t ht
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  have hcount : Nat.card ↑((ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))))
        ∩ t • D)
      = Nat.card ↑(D' ∩ t⁻¹ • ((T.symm ξ) +ᵥ
          (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) := by
    have hinj : Function.Injective (T.symm : (ι → ℝ) → (ι → ℝ)) := T.symm.injective
    rw [← Nat.card_image_of_injective hinj, Set.image_inter hinj]
    have h1 : T.symm '' (ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))))
        = (T.symm ξ) +ᵥ (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := by
      rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
      exact Set.image_congr' (fun z ↦ by simp [vadd_eq_add, map_add])
    have h2 : T.symm '' (t • D) = t • D' := by rw [hD', image_smul_set]
    rw [h1, h2, Set.inter_comm]
    have hbij : ↑(D' ∩ t⁻¹ • ((T.symm ξ) +ᵥ
          (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ≃
        ↑(t • D' ∩ ((T.symm ξ) +ᵥ (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) :=
      Equiv.subtypeEquiv (Equiv.smulRight ht0) (fun x ↦ by
        simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ ht0,
          ← Set.mem_inv_smul_set_iff₀ ht0])
    rw [Nat.card_congr hbij]
  rw [hcount, ← hvolD']
  exact abs_cardR_translate_sub_volume_le hD'bdd hD'meas hφ'lip hcov' (T.symm ξ) ht

end Cox.Chebotarev
