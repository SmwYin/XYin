/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Generators of `Γ(2)` and slash invariance

We define the elements `α = [[1, 2], [0, 1]]`, `β = [[1, 0], [2, 1]]` and `-I` of `Γ(2)` and prove
that they generate `Γ(2)` (`Γ2_generate`). As a corollary, invariance of a function under the
weight-`k` slash action of `Γ(2)` only needs to be checked on these three elements
(`slashaction_generators_Γ2`). For `SL(2, ℤ)` and its generators `S`, `T` see mathlib's
`SlashInvariantForm.slash_action_generators_SL2Z`.
-/

@[expose] public section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane CongruenceSubgroup ModularGroup

local notation "Γ " n:100 => Gamma n

/-- The generator `α = [[1, 2], [0, 1]] = T²` of `Γ(2)`. -/
def α : Γ 2 := by
  let A : SL(2, ℤ) := ⟨!![1, 2; 0, 1], by simp⟩
  exact ⟨A, Gamma_mem.mpr (by decide)⟩

/-- The generator `β = [[1, 0], [2, 1]]` of `Γ(2)`. -/
def β : Γ 2 := by
  let A : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by simp⟩
  exact ⟨A, Gamma_mem.mpr (by decide)⟩

/-- The element `-I` of `Γ(2)`. -/
def negI : Γ 2 := by
  let A : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by simp⟩
  exact ⟨A, Gamma_mem.mpr (by decide)⟩

theorem α_eq_T_sq :
    α = ⟨T ^ 2, by simp only [Gamma_mem, Fin.isValue, SpecialLinearGroup.coe_pow]; decide⟩ := by
  decide

theorem β_eq_negI_mul_S_mul_α_inv_mul_S : β = negI * S * α⁻¹ * S := by decide

theorem ModularGroup.modular_negI_sq : negI ^ 2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem ModularGroup.modular_negI_inv : negI⁻¹ = negI := by decide

section slash_action

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

open ModularForm

theorem modular_negI_smul : negI.1 • z = z := by rw [specialLinearGroup_apply]; simp [negI]

theorem modular_slash_negI_of_even (hk : Even k) : f ∣[k] negI.1 = f := by
  ext x; rw [slash_action_eq'_iff, modular_negI_smul]; simp [negI, hk.neg_one_zpow]

/-- The slash action of `T` is translation by `1` (the analogue of mathlib's
`SlashInvariantForm.slash_S_apply`). -/
theorem modular_slash_T_apply : (f ∣[k] T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, ModularGroup.denom_apply, UpperHalfPlane.modular_T_smul]
  simp

end slash_action

section slashaction_generators

/-- The matrix `α ^ k` equals `[[1, 2k], [0, 1]]`. -/
private theorem α_zpow_val (k : ℤ) : (α ^ k : SL(2, ℤ)).val = !![1, 2 * k; 0, 1] := by
  induction k using Int.induction_on with
  | zero => exact Matrix.one_fin_two
  | succ n ih =>
    simp only [zpow_add, zpow_one, SpecialLinearGroup.coe_mul, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [α]; ring
  | pred n ih =>
    simp only [zpow_sub, zpow_one, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [α]; ring

/-- The matrix `β ^ k` equals `[[1, 0], [2k, 1]]`. -/
private theorem β_zpow_val (k : ℤ) : (β ^ k : SL(2, ℤ)).val = !![1, 0; 2 * k, 1] := by
  induction k using Int.induction_on with
  | zero => exact Matrix.one_fin_two
  | succ n ih =>
    simp only [zpow_add, zpow_one, SpecialLinearGroup.coe_mul, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [β, Matrix.mul_apply]; ring
  | pred n ih =>
    simp only [zpow_sub, zpow_one, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [β, Matrix.mul_apply]; ring

lemma Γ2_c_eq_zero (A : Γ 2) (h : A.1 1 0 = 0) : A ∈ Subgroup.closure {α, β, negI} := by
  obtain ⟨A, hA⟩ := A
  change A.val 1 0 = 0 at h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, A.val 0 1 = 2 * k := by
    simp only [Gamma_mem] at hA
    erw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA
    exact hA.2.1
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have hdet := A.2
    rw [Matrix.det_fin_two] at hdet
    simpa [h] using hdet
  have hα : α ∈ Subgroup.closure {α, β, negI} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨h00, h11⟩ | ⟨h00, h11⟩
  · have heq : A = α ^ k := by
      apply Subtype.ext
      rw [α_zpow_val]
      ext i j; fin_cases i <;> fin_cases j <;> simp_all
    convert Subgroup.zpow_mem (Subgroup.closure {α, β, negI}) hα k using 1
    exact Subtype.ext heq
  · have heq : A = negI * α ^ (-k) := by
      apply Subtype.ext
      rw [SpecialLinearGroup.coe_mul, α_zpow_val]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [negI, Matrix.mul_apply, h, hk, h00, h11]
    have hn : negI ∈ Subgroup.closure {α, β, negI} :=
      Subgroup.subset_closure (by simp)
    convert Subgroup.mul_mem _ hn (Subgroup.zpow_mem _ hα (-k)) using 1
    exact Subtype.ext heq

lemma Γ2_reduce_row (a c : ℤ) (ha : Odd a) (hc : Even c) (hc0 : c ≠ 0) :
    ∃ n, |a + 2 * n * c| < |c| := by
  have h2c : 2 * c ≠ 0 := by simp [hc0]
  obtain ⟨q, r, hqr, hr0, hr2c⟩ : ∃ q r, a = 2 * c * q + r ∧ 0 ≤ r ∧ r < 2 * |c| := by
    refine ⟨a / (2 * c), a % (2 * c), by rw [Int.mul_ediv_add_emod],
      Int.emod_nonneg _ h2c, ?_⟩
    simpa using Int.emod_lt_abs _ h2c
  by_cases hr_le : r ≤ |c|
  · refine ⟨-q, ?_⟩
    by_cases hr_eq : r = c ∨ r = -c <;> [grind; exact abs_lt.mpr ⟨by grind, by grind⟩]
  · refine ⟨-q - (if c > 0 then 1 else -1), ?_⟩
    split_ifs <;> cases abs_cases c <;> grind

lemma Γ2_reduce_col (a c : ℤ) (ha : Odd a) (hc : Even c) (ha0 : a ≠ 0) :
    ∃ m, |c + 2 * m * a| < |a| := by
  obtain ⟨q, r, hqr, hr0, hra⟩ : ∃ q r, c / 2 = q * a + r ∧ 0 ≤ r ∧ r < |a| :=
    ⟨c / 2 / a, c / 2 % a, by rw [Int.ediv_mul_add_emod],
      Int.emod_nonneg _ ha0, Int.emod_lt_abs _ ha0⟩
  have hm : ∃ m, |c / 2 + m * a| ≤ (|a| - 1) / 2 := by
    by_cases hr_case : r ≤ (|a| - 1) / 2
    · exact ⟨-q, by rw [abs_le]; constructor <;> grind⟩
    · refine ⟨if a > 0 then -q - 1 else -q + 1, ?_⟩
      split_ifs <;> cases abs_cases a <;> cases ha <;> exact abs_le.mpr ⟨by grind, by grind⟩
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, ?_⟩
  norm_num [abs_le] at *
  cases abs_cases a <;> cases abs_cases (c + 2 * m * a) <;>
    nlinarith [Int.ediv_mul_cancel (show 2 ∣ c from even_iff_two_dvd.mp hc),
      Int.ediv_mul_cancel (show 2 ∣ |a| - 1 from even_iff_two_dvd.mp
        (by cases abs_cases a <;> simp [*, parity_simps]))]

/-- The `(0, 0)` entry of any element of `Γ(2)` is odd. -/
private lemma Γ2_odd_00 (A : Γ 2) : Odd (A.val.val 0 0) := by
  have := A.2; simp only [Gamma_mem] at this
  exact ZMod.intCast_eq_one_iff_odd.mp this.1

/-- The `(1, 0)` entry of any element of `Γ(2)` is even. -/
private lemma Γ2_even_10 (A : Γ 2) : Even (A.val.val 1 0) := by
  have := A.2; simp only [Gamma_mem] at this
  exact even_iff_two_dvd.mpr (by erw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact this.2.2.1)

lemma Γ2_descent (A : Γ 2) (h : A.1 1 0 ≠ 0) :
    ∃ (M : Γ 2), M ∈ Subgroup.closure {α, β, negI} ∧ |(M * A).1 1 0| < |A.1 1 0| := by
  have h_odd := Γ2_odd_00 A
  have h_even := Γ2_even_10 A
  obtain ⟨n, hn⟩ := Γ2_reduce_row (A.val.val 0 0) (A.val.val 1 0) h_odd h_even h
  have ha'_odd : Odd (A.val.val 0 0 + 2 * n * A.val.val 1 0) := by simp [parity_simps, h_odd]
  have ha'_ne : A.val.val 0 0 + 2 * n * A.val.val 1 0 ≠ 0 := fun h' ↦ by simp_all
  obtain ⟨m, hm⟩ := Γ2_reduce_col _ _ ha'_odd h_even ha'_ne
  have hβ_mem : β ∈ Subgroup.closure {α, β, negI} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hα_mem : α ∈ Subgroup.closure {α, β, negI} := Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨β ^ m * α ^ n, Subgroup.mul_mem _ (Subgroup.zpow_mem _ hβ_mem _)
    (Subgroup.zpow_mem _ hα_mem _), ?_⟩
  simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow, SpecialLinearGroup.coe_mul,
    α_zpow_val, β_zpow_val, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hn hm ⊢
  convert hm.trans hn using 1
  ring_nf

theorem Γ2_generate : (⊤ : Subgroup (Γ 2)) = Subgroup.closure {α, β, negI} := by
  refine le_antisymm ?_ le_top
  intro A hA
  by_contra h_contra
  let d := sInf {n : ℕ | ∃ M ∈ Subgroup.closure {α, β, negI}, n = Int.natAbs ((M * A).val.val 1 0)}
  obtain ⟨M, hM₁, hM₂⟩ :
    ∃ M ∈ Subgroup.closure {α, β, negI}, Int.natAbs ((M * A).val.val 1 0) = d := by
    have h_nonempty :
      {n : ℕ | ∃ M ∈ Subgroup.closure {α, β, negI}, n
        = Int.natAbs ((M * A).val.val 1 0)}.Nonempty :=
      ⟨_, ⟨1, Subgroup.one_mem _, rfl⟩⟩
    exact (Nat.sInf_mem h_nonempty) |> fun ⟨M, hM₁, hM₂⟩ ↦ ⟨M, hM₁, hM₂.symm⟩
  by_cases hd_pos : d > 0
  · obtain ⟨M', hM'₁, hM'₂⟩ : ∃ M' ∈ Subgroup.closure {α, β, negI},
      Int.natAbs ((M' * (M * A)).val.val 1 0) < d := by
      convert Γ2_descent (M * A) fun h ↦ _ <;> simp_all [← hM₂, ← Int.ofNat_lt]
    have h_inf_le :
      ∀ n ∈ {n : ℕ | ∃ M ∈ Subgroup.closure {α, β, negI}, n
        = Int.natAbs ((M * A).val.val 1 0)}, d ≤ n :=
      fun n hn ↦ Nat.sInf_le hn
    exact not_lt_of_ge (h_inf_le _ ⟨M' * M, Subgroup.mul_mem _ hM'₁ hM₁, rfl⟩)
      (by simpa [mul_assoc] using hM'₂)
  · have hMA_zero : (M * A).val.val 1 0 = 0 :=
      Int.natAbs_eq_zero.mp (hM₂.trans (le_antisymm (le_of_not_gt hd_pos) (Nat.zero_le _)))
    exact h_contra
      (by simpa only [inv_mul_cancel_left] using
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hM₁) (Γ2_c_eq_zero _ hMA_zero))

/-- If `G` is generated by a set `s ⊆ G`, then invariance under the slash action of `G` only
needs to be checked on `s`. (For subgroups of `GL(2, ℝ)` see mathlib's
`SlashInvariantForm.slash_action_generators`.) -/
theorem slashaction_generators'
    (f : ℍ → ℂ) {G : Subgroup SL(2, ℤ)} (s : Set G) (hG : ⊤ = Subgroup.closure s) (k : ℤ) :
    (∀ γ : G, f ∣[k] γ.1 = f) ↔ (∀ γ ∈ s, f ∣[k] γ.1 = f) := by
  constructor <;> intro h
  · intro γ _
    exact h _
  · intro ⟨γ, hγ⟩
    -- key idea: this lemma allows induction on the "words" of the group
    apply Subgroup.closure_induction (G := G) (p := fun γ _ ↦ f ∣[k] γ.1 = f) (k := s) ?_ ?_
    · intro _ _ _ _ hf₁ hf₂
      rw [Subgroup.coe_mul, SlashAction.slash_mul, hf₁, hf₂]
    · intro x _ hf
      rw [← hf, ← SlashAction.slash_mul]
      simp [hf]
    · simp [← hG]
    · intro γ hγ
      exact h γ hγ
    · exact SlashAction.slash_one k f

/-- A function is invariant under the weight-`k` slash action of `Γ(2)` as soon as it is
invariant under `α`, `β` and `-I`. -/
theorem slashaction_generators_Γ2
    (f : ℍ → ℂ) (k : ℤ) (hα : f ∣[k] α.1 = f) (hβ : f ∣[k] β.1 = f) (hnegI : f ∣[k] negI.1 = f) :
    (∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 2), f ∣[k] γ = f) := by
  rintro γ ⟨A, hA₁, rfl⟩
  change f ∣[k] A = f
  refine (slashaction_generators' f {α, β, negI} Γ2_generate k).mpr ?_ ⟨_, hA₁⟩
  intro γ hγ
  rcases hγ with (rfl | rfl | rfl | _) <;> assumption

end slashaction_generators
