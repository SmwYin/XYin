import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Order.CompletePartialOrder

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical



open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup


theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  /-
  simp only [comp_apply]
  have h1 := Function.Periodic.boundedAtFilter_cuspFunction (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)
    (bounded_at_infty_comp_ofComplex f)
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) ?_ ?_ ?_).continuousAt.tendsto
    apply SlashInvariantFormClass.periodic_comp_ofComplex
    simp only [eventually_comap, eventually_atTop, ge_iff_le]
    use 1
    intro b hb a ha
    apply ModularFormClass.differentiableAt_comp_ofComplex (z := a)
    rw [ha]
    linarith
    apply ModularFormClass.bounded_at_infty_comp_ofComplex
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  apply Metric.ball_mem_nhds
  exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0
  -/
  sorry
/-
theorem cuspFunction_mul_zero (n : ℕ) (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b) [inst : NeZero n] :
    cuspFunction n (f.mul g) 0 = cuspFunction n f 0 * cuspFunction n g 0 := by
  rw [cuspFunction, Periodic.cuspFunction ]
  simp only [mul_coe, update_self]
  apply Filter.Tendsto.limUnder_eq
  have : (⇑f * ⇑g) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) * (⇑g ∘ ↑ofComplex) := by
    ext y
    simp only [comp_apply, Pi.mul_apply]
  rw [this]
  apply Filter.Tendsto.mul
  · apply modform_tendto_ndhs_zero
  · apply modform_tendto_ndhs_zero

lemma qExpansion_mul_coeff_zero (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)).coeff 0 =
      (((qExpansion n f)).coeff 0) * ((qExpansion n g)).coeff  0 := by
    simp_rw [qExpansion_coeff ]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    apply cuspFunction_mul_zero


lemma cuspFunction_mul (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : cuspFunction n (f.mul g) = cuspFunction n f * cuspFunction n g := by
    ext z
    by_cases h : z = 0
    rw [h]
    simp only [Pi.mul_apply]
    apply cuspFunction_mul_zero
    simp_rw [cuspFunction, Periodic.cuspFunction]
    simp only [mul_coe, ne_eq, h, not_false_eq_true, update_of_ne, comp_apply, Pi.mul_apply]
-/

theorem derivWithin_mul2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hd : DifferentiableOn ℂ g s) :
    s.restrict (derivWithin (f * g) s) =
      s.restrict (derivWithin f s * g  + f  * derivWithin g s)  := by
  ext y
  simp
  rw [derivWithin_mul]
  exact hf y y.2
  exact hd y y.2


/-
lemma iteratedDerivWithin_mul (f g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (m : ℕ)
    (hf : ContDiffOn ℂ ⊤ f s)(hg : ContDiffOn ℂ ⊤ g s) :
    iteratedDerivWithin m (f * g) s x =
    ∑ i ∈ Finset.range m.succ, (m.choose i) * (iteratedDerivWithin i f s x) * (iteratedDerivWithin (m - i) g s x) := by
  induction m generalizing f g with
  | zero =>
  simp only [iteratedDerivWithin_zero, Pi.mul_apply, Nat.succ_eq_add_one, zero_add,
    Finset.range_one, zero_le, Nat.sub_eq_zero_of_le, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, one_mul]
  | succ m hm =>
  have h1 := derivWithin_mul2 f g s (hf.differentiableOn (by simp)) (hg.differentiableOn (by simp))
  have h2 : (fun y => f y * g y) = f * g := by
    ext y
    simp
  rw [iteratedDerivWithin_succ']
  have hset : s.EqOn (derivWithin (f * g) s) (derivWithin f s * g + f * derivWithin g s) := by
    intro z hz
    aesop
  rw [iteratedDerivWithin_congr hset, iteratedDerivWithin_add, hm, hm]
  simp_rw [←iteratedDerivWithin_succ']
  have := Finset.sum_choose_succ_mul (fun i => fun j =>
    ((iteratedDerivWithin i f s x) * (iteratedDerivWithin j g s x)) ) m
  simp at *
  rw [show m + 1 + 1 = m + 2 by ring]
  simp_rw [← mul_assoc] at *
  rw [this, add_comm]
  congr 1
  apply Finset.sum_congr
  rfl
  intros i hi
  congr
  simp at hi
  omega
  exact hf
  exact ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
  exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := ⊤) (by simp)
  exact hg
  exact hx
  exact hs.uniqueDiffOn
  apply ContDiffOn.mul
  exact ContDiffOn.derivWithin hf (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
  apply ContDiffOn.of_le hg (by simp)
  exact hx
  apply ContDiffOn.mul
  apply ContDiffOn.of_le hf (by simp)
  apply ContDiffOn.derivWithin hg (by exact IsOpen.uniqueDiffOn hs) (m := m) (by simp)
  exact hx
  exact hx
-/


lemma iteratedDeriv_eq_iteratedDerivWithin (n : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
  (z : ℂ) (hz : z ∈ s) : iteratedDeriv n f z = iteratedDerivWithin n f s z := by
  rw [← iteratedDerivWithin_univ]
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_congr_set]
  apply EventuallyEq.symm
  rw [eventuallyEq_univ]
  exact IsOpen.mem_nhds hs hz

lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)[NeZero n] :
    (qExpansion n (f.mul g)) = ((qExpansion n f)) * ((qExpansion n g)) := by
  /-
  ext m
  induction m with
  | zero =>
  simpa using qExpansion_mul_coeff_zero n a b f g
  | succ m hm =>
  simp_rw [PowerSeries.coeff_mul ,qExpansion_coeff, cuspFunction_mul ] at *
  have :=iteratedDerivWithin_mul (f := cuspFunction n f) (g := cuspFunction n g) (Metric.ball 0 1) (isOpen_ball) 0 (by simp) (m+1) ?_ ?_
  simp_rw [← iteratedDeriv_eq_iteratedDerivWithin (m+1) _ (Metric.ball 0 1) (isOpen_ball) 0
    (by simp)] at this
  conv at this =>
    enter [2,2]
    intro n
    rw [← iteratedDeriv_eq_iteratedDerivWithin n _ (Metric.ball 0 1) (isOpen_ball) 0 (by simp)]
    rw [← iteratedDeriv_eq_iteratedDerivWithin (m + 1 -n) _ (Metric.ball 0 1) (isOpen_ball) 0
      (by simp)]
  rw [this]
  simp only [Nat.succ_eq_add_one]
  have h0 : ((m+1)! : ℂ) ≠  0 := by
    norm_cast
    exact Nat.factorial_ne_zero (m + 1)
  rw [inv_mul_eq_iff_eq_mul₀ h0, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  simp only [Nat.succ_eq_add_one]
  have ht (x : ℕ) : ↑(m + 1)! *
    ((↑x !)⁻¹ * iteratedDeriv x (cuspFunction n f) 0 *
      ((↑(m + 1 - x)!)⁻¹ * iteratedDeriv (m + 1 - x) (cuspFunction n g) 0)) =
      (↑(m + 1)! *
    ((↑x !)⁻¹ * ((↑(m + 1 - x)!)⁻¹) * iteratedDeriv x (cuspFunction n f) 0 *
      iteratedDeriv (m + 1 - x) (cuspFunction n g) 0)) := by ring
  conv =>
    enter [2,2]
    intro x
    rw [ht x]
  apply Finset.sum_congr
  rfl
  intro x hx
  simp_rw [← mul_assoc]
  congr
  simp only [Finset.mem_range] at hx
  rw [Nat.cast_choose ℂ (b := m + 1) (a := x)]
  field_simp
  omega
  · refine DifferentiableOn.contDiffOn ?_ (isOpen_ball)
    intro y hy
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_cuspFunction
    simpa using hy
  · refine DifferentiableOn.contDiffOn ?_ (isOpen_ball)
    intro y hy
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_cuspFunction
    simpa using hy
  -/
  sorry

/-
lemma cuspFunction_sub [NeZero n] (f g : ModularForm Γ(n) k) :
    cuspFunction n (f - g) = cuspFunction n f - cuspFunction n g := by
  simp only [cuspFunction, Periodic.cuspFunction]
  ext y
  by_cases hy : y = 0
  conv =>
    enter [1]
    rw [hy]
  rw [hy]
  simp only [update_self]
  have : ((⇑f - ⇑g) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = (⇑f ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n
      - (⇑g ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n := by
    ext y
    simp
  simp only [coe_sub, Pi.sub_apply, update_self] at *
  rw [this]
  rw [Filter.Tendsto.limUnder_eq]
  apply Tendsto.sub
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero f n
    simp only [comp_apply] at *
    aesop
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero g n
    simp only [comp_apply] at *
    aesop
  · simp [hy]


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma qExpansion_sub (f g : ModularForm Γ(1) k) : (qExpansion 1 (f - g)) =
    (qExpansion 1 f) - (qExpansion 1 g) := by
  /-
  ext m
  simp_rw [qExpansion]
  simp
  rw [cuspFunction_sub]
  rw [← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1)]
  rw [iteratedDerivWithin_sub]
  · ring
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine (DifferentiableOn.contDiffOn (E := ℂ) ?_ ?_).contDiffWithinAt ?_
    intro x hx
    refine DifferentiableAt.differentiableWithinAt ?_
    refine differentiableAt_cuspFunction 1 f ?_
    simpa using hx
    exact  isOpen_ball
    simp
  · refine (DifferentiableOn.contDiffOn (E := ℂ) ?_ ?_).contDiffWithinAt ?_
    intro x hx
    refine DifferentiableAt.differentiableWithinAt ?_
    refine differentiableAt_cuspFunction 1 g ?_
    simpa using hx
    exact  isOpen_ball
    simp
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero 1 g
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero 1 f
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    refine AnalyticAt.sub ?_ ?_
    exact analyticAt_cuspFunction_zero 1 f
    exact analyticAt_cuspFunction_zero 1 g
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  -/
  sorry


lemma cuspFunction_add [NeZero n] (f g : ModularForm Γ(n) k) :
    cuspFunction n (f + g) = cuspFunction n f + cuspFunction n g := by
  simp only [cuspFunction, Periodic.cuspFunction, coe_add]
  ext y
  by_cases hy : y = 0
  conv =>
    enter [1]
    rw [hy]
  rw [hy]
  simp only [update_self, Pi.add_apply ]
  have : ((⇑f + ⇑g) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = (⇑f ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n
      + (⇑g ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n := by
    ext y
    simp
  simp only at *
  rw [this]
  rw [Filter.Tendsto.limUnder_eq]
  apply Tendsto.add
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero f n
    simp only [comp_apply] at *
    aesop
  · apply tendsto_nhds_limUnder
    have := modform_tendto_ndhs_zero g n
    simp only [comp_apply] at *
    aesop
  · simp [hy]


lemma qExpansion_add (f g : ModularForm Γ(1) k) : (qExpansion 1 (f + g)) =
    (qExpansion 1 f) + (qExpansion 1 g) := by
  /-
  ext m
  simp_rw [qExpansion]
  simp
  rw [cuspFunction_add]
  rw [← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1),
  ← iteratedDerivWithin_eq_iteratedDeriv (s := Metric.ball 0 1)]
  rw [iteratedDerivWithin_add]
  · ring
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine (DifferentiableOn.contDiffOn (E := ℂ) ?_ ?_).contDiffWithinAt ?_
    intro x hx
    refine DifferentiableAt.differentiableWithinAt ?_
    refine differentiableAt_cuspFunction 1 f ?_
    simpa using hx
    exact  isOpen_ball
    simp
  · refine (DifferentiableOn.contDiffOn (E := ℂ) ?_ ?_).contDiffWithinAt ?_
    intro x hx
    refine DifferentiableAt.differentiableWithinAt ?_
    refine differentiableAt_cuspFunction 1 g ?_
    simpa using hx
    exact  isOpen_ball
    simp
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero 1 g
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    exact analyticAt_cuspFunction_zero 1 f
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  · refine IsOpen.uniqueDiffOn ?_
    exact isOpen_ball
  · refine AnalyticAt.contDiffAt ?_
    refine AnalyticAt.add ?_ ?_
    exact analyticAt_cuspFunction_zero 1 f
    exact analyticAt_cuspFunction_zero 1 g
  · refine mem_ball_self ?_
    exact Real.zero_lt_one
  -/
  sorry
-/

lemma IteratedDeriv_smul (a : ℂ)  (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (a • f) = a • iteratedDeriv m f  := by
  induction m with
  | zero => simp
  | succ m hm =>
  rw [iteratedDeriv_succ, iteratedDeriv_succ]
  rw [hm]
  ext x
  rw [@Pi.smul_def]
  exact deriv_const_smul' a (f := iteratedDeriv m f) (x := x)


lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  /-
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · simp_rw [h, cuspFunction,Periodic.cuspFunction]
      simp
      rw [Filter.limUnder_eq_iff ]
      have hl : ((a • ⇑f) ∘ ↑ofComplex) ∘ Periodic.invQParam ↑n = fun x => a * (f ∘ ↑ofComplex) (Periodic.invQParam ↑n x) := by
        simp only [comp_apply]
        ext y
        simp
      rw [hl]
      simp
      apply Filter.Tendsto.const_mul
      have := modform_tendto_ndhs_zero f _
      simp at this
      convert this
      rw [Filter.limUnder_eq_iff ]
      apply this
      aesop
      have := modform_tendto_ndhs_zero (a • f) _
      aesop
    · simp only [cuspFunction, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp only [comp_apply]
      simp
  rw [this]
  simp only [PowerSeries.coeff_mk]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
  -/
  sorry

/-
lemma qExpansion_smul (a : ℂ) (f : CuspForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  /-
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · rw [h]
      have h0 := CuspFormClass.cuspFunction_apply_zero n (a • f)
      have h1 := CuspFormClass.cuspFunction_apply_zero n f
      simp only [h0, Pi.smul_apply, h1, smul_eq_mul, mul_zero]
    · simp only [cuspFunction, CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp only [PowerSeries.coeff_mk]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
  -/
  sorry
-/

instance : FunLike (ℍ → ℂ) ℍ ℂ := { coe := fun ⦃a₁⦄ ↦ a₁, coe_injective' := fun ⦃_ _⦄ a ↦ a}

lemma qExpansion_ext (f g : ℍ → ℂ) (h : f = g) : qExpansion 1 f =
    qExpansion 1 g := by
  rw [h]

lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  simp_rw [qExpansion]
  ext m
  simp only [PowerSeries.coeff_mk, mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]
  left
  congr 1
  simp_rw [cuspFunction, Periodic.cuspFunction]
  rw [h]

/-
lemma qExpansion_of_mul (a b : ℤ) (f : ModularForm Γ(1) a) (g : ModularForm Γ(1) b) :
  qExpansion 1 (((((DirectSum.of (ModularForm Γ(1)) a ) f)) * ((DirectSum.of (ModularForm Γ(1)) b ) g)) (a + b)) =
    (qExpansion 1 f) * (qExpansion 1 g) := by
  /-
  rw [DirectSum.of_mul_of]
  rw [← qExpansion_mul_coeff]
  apply qExpansion_ext2
  ext z
  simp
  rfl
  -/
  sorry
-/
@[simp] --generalize this away from ℂ
lemma IteratedDeriv_zero_fun (n : ℕ) (z : ℂ): iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
  rw [iteratedDeriv_succ']
  simp [hn]

lemma iteratedDeriv_const_eq_zero (m : ℕ) (hm : 0 < m) (c : ℂ) :
    iteratedDeriv m (fun _ : ℂ => c) = fun _ : ℂ => 0 := by
  ext z
  have := iteratedDeriv_const_add hm (f := fun (x : ℂ) => (0 : ℂ)) c (x := z)
  simpa only [add_zero, IteratedDeriv_zero_fun] using this

lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
  qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k ) f) ^ n) (n * k)) = (qExpansion 1 f) ^ n := by
  sorry
  /-
  induction n with
  | zero =>
    simp
    rw [show 0 * k = 0 by ring]
    have hq : qExpansion 1 ((1 : ModularForm Γ(1) 0)) = 1 := by
      have : (cuspFunction 1 ((1 : ModularForm Γ(1) 0))) = 1 := by
        simp only [cuspFunction, Periodic.cuspFunction]
        ext z
        simp
        by_cases hz : z = 0
        rw [hz]
        simp
        apply Filter.Tendsto.limUnder_eq
        apply tendsto_const_nhds
        simp [hz]
      rw [qExpansion]
      rw [this]
      ext m
      simp
      by_cases hm : m = 0
      rw [hm]
      simp
      simp [hm]
      right
      have hmp : 0 < m := by omega
      have := iteratedDeriv_const_eq_zero m hmp 1
      have ht := congr_fun this 0
      apply ht
    rw [← hq]
    apply qExpansion_ext2
    rfl
  | succ n hn =>
  rw [pow_succ, pow_succ]
  rw [show ↑(n + 1) * k = (n • k) + k by simp; ring]
  rw [DirectSum.ofPow] at *
  rw [qExpansion_of_mul]
  congr
  rw [← hn]
  apply qExpansion_ext2
  ext z
  rw [show n * k = n • k by rfl]
  simp
  -/

/-
lemma qExpansion_injective (n : ℕ) [NeZero n] (f : ModularForm Γ(n) k) :
    qExpansion n f = 0 ↔ f = 0 := by
  /-
  constructor
  intro h
  ext z
  have := (hasSum_qExpansion n f z).tsum_eq
  rw [← this]
  rw [h]
  simp
  intro h
  have : Periodic.cuspFunction n 0 = 0 := by
    ext z
    rw [Periodic.cuspFunction]
    by_cases hz : z = 0
    rw [hz]
    simp
    apply Filter.Tendsto.limUnder_eq
    refine NormedAddCommGroup.tendsto_nhds_zero.mpr ?_
    simp
    simp [hz]
  rw [qExpansion, cuspFunction, h]
  simp
  rw [this]
  ext y
  simp
  right
  apply IteratedDeriv_zero_fun
  -/
  sorry

lemma qExpansion_zero [NeZero n] : qExpansion n (0 : ModularForm Γ(n) k) = 0 := by
  rw [qExpansion_injective]
-/
