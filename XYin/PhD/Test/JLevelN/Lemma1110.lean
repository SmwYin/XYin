import Mathlib
import XYin.PhD.Test.JLevelN.JN

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

/-!
# Cox Lemma 11.10(ii): level-one functions are polynomial in `j`

This file formalises the Cox Lemma 11.10(ii) route for level-one modular
functions that are holomorphic on `ℍ` and meromorphic at the cusp: such a
function is a polynomial in `j`.  The proof includes local q-expansion
computations used to identify and cancel the principal part of `j` at the cusp.
-/

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

namespace Test

open UpperHalfPlane

noncomputable section

section modularEquation

/-! ## Level-one constant criteria

These are valence-formula consequences used in the Cox Theorem 11.9(i) route.
They supply the bounded/analytic base case behind Lemma 11.10.
-/

section LevelOneConstantCriteria

/-- A plain weight-zero level-one modular function that is holomorphic on `ℍ` and bounded
at every cusp is constant.  The cusp hypothesis is given as boundedness at infinity after
all `SL₂(ℤ)` translates, matching `bounded_at_cusps_of_bounded_at_infty`. -/
theorem levelOne_weightZero_constant_of_slash_bounded {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f)
    (hbdd : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (f ∣[(0 : ℤ)] γ)) :
    ∃ c : ℂ, f = Function.const ℍ c := by
  let F : ModularForm (CongruenceSubgroup.Gamma 1) 0 := {
    toFun := f
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, rfl⟩ := hγ
      exact hslash γ'
    holo' := hmdiff
    bdd_at_cusps' := fun hc =>
      bounded_at_cusps_of_bounded_at_infty hc fun A hA => by
        obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hA
        simpa using hbdd γ
  }
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  exact ⟨c, by simpa [F] using hc⟩

/-- A level-one weight-zero invariant holomorphic function is constant if it is bounded at
`∞`; invariance supplies the boundedness of all `SL₂(ℤ)` translates. -/
theorem levelOne_weightZero_constant_of_slash_bounded_at_infty {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    ∃ c : ℂ, f = Function.const ℍ c :=
  levelOne_weightZero_constant_of_slash_bounded hslash hmdiff fun γ => by
    simpa [hslash γ] using hbdd

/-- A level-one weight-zero invariant holomorphic function that vanishes at `∞` is zero. -/
theorem levelOne_weightZero_eq_zero_of_slash_zero_at_infty {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f)
    (hzero : IsZeroAtImInfty f) :
    f = 0 := by
  obtain ⟨c, hc⟩ :=
    levelOne_weightZero_constant_of_slash_bounded_at_infty hslash hmdiff
      hzero.isBoundedAtImInfty
  have hc0 : c = 0 := by
    rw [hc] at hzero
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  ext z
  simp [hc, hc0]

/-- If the level-one cusp function of a periodic plain function is analytic at `0`, then
the original function is bounded at `∞`. -/
theorem isBoundedAtImInfty_of_analyticAt_cuspFunction_one {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (han : AnalyticAt ℂ (cuspFunction 1 f) 0) :
    IsBoundedAtImInfty f := by
  have hlim_cusp :
      Tendsto (fun τ : ℍ => cuspFunction 1 f (𝕢 (1 : ℝ) τ)) atImInfty
        (nhds (cuspFunction 1 f 0)) :=
    han.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) (by norm_num))
  have hfun : (fun τ : ℍ => cuspFunction 1 f (𝕢 (1 : ℝ) τ)) = f := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction (h := 1) (f := f) τ (by norm_num) hfper
  have hlim : Tendsto f atImInfty (nhds (cuspFunction 1 f 0)) := by
    simpa [hfun] using hlim_cusp
  exact hlim.isBigO_one ℝ

/-- A level-one weight-zero invariant holomorphic function whose cusp function is analytic at
`0` is constant. -/
theorem levelOne_weightZero_constant_of_slash_analyticAt_cusp {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f)
    (han : AnalyticAt ℂ (cuspFunction 1 f) 0) :
    ∃ c : ℂ, f = Function.const ℍ c := by
  have hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    let F : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 0 := {
      toFun := f
      slash_action_eq' := fun γ hγ => by
        rw [Subgroup.mem_map] at hγ
        obtain ⟨γ', _, rfl⟩ := hγ
        exact hslash γ'
    }
    have hfperF : Periodic (F ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
      SlashInvariantFormClass.periodic_comp_ofComplex F (by simp)
    simpa [F] using hfperF
  exact levelOne_weightZero_constant_of_slash_bounded_at_infty hslash hmdiff
    (isBoundedAtImInfty_of_analyticAt_cuspFunction_one hfper han)

/-- Pole-order zero at the level-one cusp is the analytic base case for the weight-zero
constant criterion. -/
theorem levelOne_weightZero_constant_of_slash_poleOrder_zero {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f)
    (hmero : MeromorphicAt (cuspFunction 1 f) 0) (hpole : poleOrder 1 f = 0) :
    ∃ c : ℂ, f = Function.const ℍ c := by
  exact levelOne_weightZero_constant_of_slash_analyticAt_cusp hslash hmdiff
    ((analyticAt_iff (h := 1) (f := f) hmero).2 hpole)

end LevelOneConstantCriteria

/-! ## Polynomial expressions in `j`

This is the Cox Lemma 11.10(ii) polynomial-in-`j` step, in the setting of
functions holomorphic on `ℍ` and meromorphic at the level-one cusp.
-/

section PolynomialInJ

/-- Functions of the form `P(j)`, used in Cox Lemma 11.10(ii) to cancel the
principal part at the cusp. -/
noncomputable def polynomialInJ (P : Polynomial ℂ) : ℍ → ℂ :=
  fun z => P.eval (j z)

/-- The level-one `j`-function is manifold-differentiable on the upper half-plane. -/
theorem j_MDifferentiable : MDiff j := by
  have hfun : jN (1 : ℕ+) = j := by
    funext z
    change j ((1 : ℕ+) • z) = j z
    congr 1
    ext
    simp [natPosSMul_apply]
  rw [← hfun]
  exact jN_MDifferentiable (1 : ℕ+)

/-- Every polynomial expression `P(j)` is invariant under the weight-zero slash action. -/
theorem polynomialInJ_slashInvariant (P : Polynomial ℂ) (γ : SL(2, ℤ)) :
    polynomialInJ P ∣[(0 : ℤ)] γ = polynomialInJ P := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, polynomialInJ]
  rw [j_invariant γ z]

/-- Every polynomial expression `P(j)` is manifold-differentiable on `ℍ`. -/
theorem polynomialInJ_MDifferentiable (P : Polynomial ℂ) :
    MDiff (polynomialInJ P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext z
      simp [polynomialInJ]
  | monomial n a =>
      convert (j_MDifferentiable.pow n).const_smul a using 1
      ext z
      simp [polynomialInJ]

/-- On a punctured cusp neighbourhood, the cusp function of `P(j)` is `P` applied
to the cusp function of `j`. -/
private lemma polynomialInJ_cuspFunction_eventuallyEq (P : Polynomial ℂ) :
    (fun q : ℂ => P.eval (cuspFunction 1 j q)) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      cuspFunction 1 (polynomialInJ P) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hP :
      cuspFunction 1 (polynomialInJ P) q =
        polynomialInJ P (UpperHalfPlane.ofComplex (Periodic.invQParam 1 q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero (1 : ℝ)
        ((polynomialInJ P) ∘ UpperHalfPlane.ofComplex) hq0)
  have hj :
      cuspFunction 1 j q =
        j (UpperHalfPlane.ofComplex (Periodic.invQParam 1 q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero (1 : ℝ)
        (j ∘ UpperHalfPlane.ofComplex) hq0)
  rw [hP, hj]
  rfl

/-- Enumerate convolution pairs with total index `2`. -/
private lemma antidiagonal_two_local :
    Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Enumerate convolution pairs with total index `3`. -/
private lemma antidiagonal_three_local :
    Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Enumerate convolution pairs with total index `4`. -/
private lemma antidiagonal_four_local :
    Finset.antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Enumerate convolution pairs with total index `5`. -/
private lemma antidiagonal_five :
    Finset.antidiagonal 5 = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Enumerate convolution pairs with total index `6`. -/
private lemma antidiagonal_six_local :
    Finset.antidiagonal 6 =
      {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Enumerate convolution pairs with total index `7`. -/
private lemma antidiagonal_seven_local :
    Finset.antidiagonal 7 =
      {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp
  omega

/-- Coefficient of `E₄` at `q^0` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_zero_local : (qExpansion 1 E4).coeff 0 = 1 := by
  simpa [E4] using congr_fun E4_q_exp 0

/-- Constant coefficient of `E₄` in the local q-expansion computation. -/
private lemma E4_qExpansion_constantCoeff_local :
    PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E4_qExpansion_coeff_zero_local

/-- Coefficient of `E₄` at `q^1` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_one_local : (qExpansion 1 E4).coeff 1 = 240 := by
  simpa [E4] using congr_fun E4_q_exp 1

/-- Coefficient of `E₄` at `q^2` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_two_local : (qExpansion 1 E4).coeff 2 = 2160 := by
  have h := congr_fun E4_q_exp 2
  norm_num [ArithmeticFunction.sigma] at h ⊢
  exact h

/-- Coefficient of `E₄` at `q^3` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_three_local : (qExpansion 1 E4).coeff 3 = 6720 := by
  have h := congr_fun E4_q_exp 3
  norm_num [ArithmeticFunction.sigma] at h ⊢
  exact h

/-- Coefficient of `E₄` at `q^4` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_four_local : (qExpansion 1 E4).coeff 4 = 17520 := by
  have h : (qExpansion 1 E4).coeff 4 = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := by
    simpa [E4] using (congr_fun E4_q_exp 4)
  have hsigma : ArithmeticFunction.sigma 3 4 = 73 := by
    decide
  calc
    _ = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := h
    _ = (240 : ℂ) * 73 := by simp [hsigma]
    _ = 17520 := by norm_num

/-- Coefficient of `E₄` at `q^5` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_five_local : (qExpansion 1 E4).coeff 5 = 30240 := by
  have h : (qExpansion 1 E4).coeff 5 = (240 : ℂ) * ArithmeticFunction.sigma 3 5 := by
    simpa [E4] using (congr_fun E4_q_exp 5)
  have hsigma : ArithmeticFunction.sigma 3 5 = 126 := by
    decide
  calc
    _ = (240 : ℂ) * ArithmeticFunction.sigma 3 5 := h
    _ = (240 : ℂ) * 126 := by simp [hsigma]
    _ = 30240 := by norm_num

/-- Coefficient of `E₄` at `q^6` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_six_local : (qExpansion 1 E4).coeff 6 = 60480 := by
  have h : (qExpansion 1 E4).coeff 6 = (240 : ℂ) * ArithmeticFunction.sigma 3 6 := by
    simpa [E4] using (congr_fun E4_q_exp 6)
  have hsigma : ArithmeticFunction.sigma 3 6 = 252 := by
    decide
  calc
    _ = (240 : ℂ) * ArithmeticFunction.sigma 3 6 := h
    _ = (240 : ℂ) * 252 := by simp [hsigma]
    _ = 60480 := by norm_num

/-- Coefficient of `E₄` at `q^7` used in the local q-expansion computation. -/
private lemma E4_qExpansion_coeff_seven_local : (qExpansion 1 E4).coeff 7 = 82560 := by
  have h : (qExpansion 1 E4).coeff 7 = (240 : ℂ) * ArithmeticFunction.sigma 3 7 := by
    simpa [E4] using (congr_fun E4_q_exp 7)
  have hsigma : ArithmeticFunction.sigma 3 7 = 344 := by
    decide
  calc
    _ = (240 : ℂ) * ArithmeticFunction.sigma 3 7 := h
    _ = (240 : ℂ) * 344 := by simp [hsigma]
    _ = 82560 := by norm_num

/-- Coefficient of `E₆` at `q^0` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_zero_local : (qExpansion 1 E6).coeff 0 = 1 := by
  simpa [E6] using congr_fun E6_q_exp 0

/-- Constant coefficient of `E₆` in the local q-expansion computation. -/
private lemma E6_qExpansion_constantCoeff_local :
    PowerSeries.constantCoeff (qExpansion 1 E6) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E6_qExpansion_coeff_zero_local

/-- Coefficient of `E₆` at `q^1` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_one_local : (qExpansion 1 E6).coeff 1 = -504 := by
  simpa [E6] using congr_fun E6_q_exp 1

/-- Coefficient of `E₆` at `q^2` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_two_local : (qExpansion 1 E6).coeff 2 = -16632 := by
  have h := congr_fun E6_q_exp 2
  norm_num [ArithmeticFunction.sigma] at h ⊢
  exact h

/-- Coefficient of `E₆` at `q^3` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_three_local : (qExpansion 1 E6).coeff 3 = -122976 := by
  have h := congr_fun E6_q_exp 3
  norm_num [ArithmeticFunction.sigma] at h ⊢
  exact h

/-- Coefficient of `E₆` at `q^4` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_four_local : (qExpansion 1 E6).coeff 4 = -532728 := by
  have h : (qExpansion 1 E6).coeff 4 = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := by
    simpa [E6] using (congr_fun E6_q_exp 4)
  have hsigma : ArithmeticFunction.sigma 5 4 = 1057 := by
    decide
  calc
    _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := h
    _ = -(504 : ℂ) * 1057 := by simp [hsigma]
    _ = -532728 := by norm_num

/-- Coefficient of `E₆` at `q^5` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_five_local : (qExpansion 1 E6).coeff 5 = -1575504 := by
  have h : (qExpansion 1 E6).coeff 5 = -(504 : ℂ) * ArithmeticFunction.sigma 5 5 := by
    simpa [E6] using (congr_fun E6_q_exp 5)
  have hsigma : ArithmeticFunction.sigma 5 5 = 3126 := by
    decide
  calc
    _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 5 := h
    _ = -(504 : ℂ) * 3126 := by simp [hsigma]
    _ = -1575504 := by norm_num

/-- Coefficient of `E₆` at `q^6` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_six_local : (qExpansion 1 E6).coeff 6 = -4058208 := by
  have h : (qExpansion 1 E6).coeff 6 = -(504 : ℂ) * ArithmeticFunction.sigma 5 6 := by
    simpa [E6] using (congr_fun E6_q_exp 6)
  have hsigma : ArithmeticFunction.sigma 5 6 = 8052 := by
    decide
  calc
    _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 6 := h
    _ = -(504 : ℂ) * 8052 := by simp [hsigma]
    _ = -4058208 := by norm_num

/-- Coefficient of `E₆` at `q^7` used in the local q-expansion computation. -/
private lemma E6_qExpansion_coeff_seven_local :
    (qExpansion 1 E6).coeff 7 = -8471232 := by
  have h : (qExpansion 1 E6).coeff 7 = -(504 : ℂ) * ArithmeticFunction.sigma 5 7 := by
    simpa [E6] using (congr_fun E6_q_exp 7)
  have hsigma : ArithmeticFunction.sigma 5 7 = 16808 := by
    decide
  calc
    _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 7 := h
    _ = -(504 : ℂ) * 16808 := by simp [hsigma]
    _ = -8471232 := by norm_num

/-- q-expansion identity identifying `E₄ ^ 3` with the cube of the `E₄` expansion. -/
private lemma qExpansion_E4_pow_three_eq_local :
    qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
  simpa [DirectSum.ofPow] using
    qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := by simp) E4 3

/-- q-expansion identity identifying `E₆ ^ 2` with the square of the `E₆` expansion. -/
private lemma qExpansion_E6_pow_two_eq_local :
    qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
  simpa [DirectSum.ofPow] using
    qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := by simp) E6 2

/-- Coefficient of `E₄ * E₄` at `q^1` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_one_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  simp only [Nat.cast_ofNat, Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one,
    and_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^2` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_two_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
  rw [PowerSeries.coeff_mul, antidiagonal_two_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, OfNat.ofNat_ne_one,
    and_self, Finset.mem_singleton, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, or_self,
    not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff, OfNat.one_ne_ofNat,
    one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^3` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_three_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
  rw [PowerSeries.coeff_mul, antidiagonal_three_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, Finset.mem_singleton, OfNat.ofNat_ne_zero,
    or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff, OfNat.one_ne_ofNat,
    Nat.reduceEqDiff, one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^4` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_four_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 4 = 7926240 := by
  rw [PowerSeries.coeff_mul, antidiagonal_four_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^5` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_five_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 5 = 37500480 := by
  rw [PowerSeries.coeff_mul, antidiagonal_five]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^6` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_six_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 6 = 135480960 := by
  rw [PowerSeries.coeff_mul, antidiagonal_six_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local,
    E4_qExpansion_coeff_six_local]
  norm_num

/-- Coefficient of `E₄ * E₄` at `q^7` used to compute `E₄ ^ 3`. -/
private lemma E4_mul_self_coeff_seven_local :
    (qExpansion 1 E4 * qExpansion 1 E4).coeff 7 = 395301120 := by
  rw [PowerSeries.coeff_mul, antidiagonal_seven_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local,
    E4_qExpansion_coeff_six_local, E4_qExpansion_coeff_seven_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^0` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_zero_local : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
  rw [qExpansion_E4_pow_three_eq_local]
  have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E4_qExpansion_coeff_zero_local
  simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]

/-- Constant coefficient of `E₄ ^ 3` in the local q-expansion computation. -/
private lemma E4_cubed_constantCoeff_local :
    PowerSeries.constantCoeff (qExpansion 1 (E4 ^ 3)) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using E4_cubed_coeff_zero_local

/-- Coefficient of `E₄ ^ 3` at `q^1` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_one_local : (qExpansion 1 (E4 ^ 3)).coeff 1 = 720 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_one]
  simp only [Nat.cast_ofNat, Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one,
    and_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff, map_mul,
    Finset.sum_singleton]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_mul_self_coeff_one_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^2` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_two_local :
    (qExpansion 1 (E4 ^ 3)).coeff 2 = 179280 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_two_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, OfNat.ofNat_ne_one,
    and_self, Finset.mem_singleton, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, or_self,
    not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff, OfNat.one_ne_ofNat,
    one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_mul_self_coeff_one_local,
    E4_mul_self_coeff_two_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^3` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_three_local :
    (qExpansion 1 (E4 ^ 3)).coeff 3 = 16954560 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_three_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, Finset.mem_singleton, OfNat.ofNat_ne_zero,
    or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff, OfNat.one_ne_ofNat,
    Nat.reduceEqDiff, one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_mul_self_coeff_one_local, E4_mul_self_coeff_two_local,
    E4_mul_self_coeff_three_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^4` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_four_local :
    (qExpansion 1 (E4 ^ 3)).coeff 4 = 396974160 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_four_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_mul_self_coeff_one_local,
    E4_mul_self_coeff_two_local, E4_mul_self_coeff_three_local,
    E4_mul_self_coeff_four_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^5` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_five_local :
    (qExpansion 1 (E4 ^ 3)).coeff 5 = 4632858720 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul, antidiagonal_five]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local,
    E4_mul_self_coeff_one_local, E4_mul_self_coeff_two_local,
    E4_mul_self_coeff_three_local, E4_mul_self_coeff_four_local,
    E4_mul_self_coeff_five_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^6` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_six_local :
    (qExpansion 1 (E4 ^ 3)).coeff 6 = 34413301440 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_six_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local,
    E4_qExpansion_coeff_six_local, E4_mul_self_coeff_one_local,
    E4_mul_self_coeff_two_local, E4_mul_self_coeff_three_local,
    E4_mul_self_coeff_four_local, E4_mul_self_coeff_five_local,
    E4_mul_self_coeff_six_local]
  norm_num

/-- Coefficient of `E₄ ^ 3` at `q^7` in the local q-expansion computation. -/
private lemma E4_cubed_coeff_seven_local :
    (qExpansion 1 (E4 ^ 3)).coeff 7 = 187477879680 := by
  rw [qExpansion_E4_pow_three_eq_local, pow_three, PowerSeries.coeff_mul,
    antidiagonal_seven_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton, map_mul]
  rw [E4_qExpansion_constantCoeff_local, E4_qExpansion_coeff_one_local,
    E4_qExpansion_coeff_two_local, E4_qExpansion_coeff_three_local,
    E4_qExpansion_coeff_four_local, E4_qExpansion_coeff_five_local,
    E4_qExpansion_coeff_six_local, E4_qExpansion_coeff_seven_local,
    E4_mul_self_coeff_one_local, E4_mul_self_coeff_two_local,
    E4_mul_self_coeff_three_local, E4_mul_self_coeff_four_local,
    E4_mul_self_coeff_five_local, E4_mul_self_coeff_six_local,
    E4_mul_self_coeff_seven_local]
  norm_num

/-- Coefficient of `E₆ ^ 2` at `q^6` used to compute `Delta`. -/
private lemma E6_squared_coeff_six_local :
    (qExpansion 1 (E6 ^ 2)).coeff 6 = 34423752384 := by
  rw [qExpansion_E6_pow_two_eq_local, pow_two, PowerSeries.coeff_mul,
    antidiagonal_six_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E6_qExpansion_constantCoeff_local, E6_qExpansion_coeff_one_local,
    E6_qExpansion_coeff_two_local, E6_qExpansion_coeff_three_local,
    E6_qExpansion_coeff_four_local, E6_qExpansion_coeff_five_local,
    E6_qExpansion_coeff_six_local]
  norm_num

/-- Coefficient of `E₆ ^ 2` at `q^7` used to compute `Delta`. -/
private lemma E6_squared_coeff_seven_local :
    (qExpansion 1 (E6 ^ 2)).coeff 7 = 187506813312 := by
  rw [qExpansion_E6_pow_two_eq_local, pow_two, PowerSeries.coeff_mul,
    antidiagonal_seven_local]
  simp only [Nat.cast_ofNat, Finset.mem_insert, Prod.mk.injEq, zero_ne_one, Nat.succ_ne_self,
    and_self, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_one, Finset.mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert, coeff_zero_eq_constantCoeff,
    OfNat.one_ne_ofNat, one_ne_zero, Finset.sum_singleton]
  rw [E6_qExpansion_constantCoeff_local, E6_qExpansion_coeff_one_local,
    E6_qExpansion_coeff_two_local, E6_qExpansion_coeff_three_local,
    E6_qExpansion_coeff_four_local, E6_qExpansion_coeff_five_local,
    E6_qExpansion_coeff_six_local, E6_qExpansion_coeff_seven_local]
  norm_num

/-- q-expansion identity for the numerator `E₄ ^ 3 - E₆ ^ 2` of `Delta`. -/
private lemma qExpansion_E4_E6_sub_local :
    qExpansion 1 (E4 ^ 3 - E6 ^ 2) =
      qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by
  calc
    _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
      have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
      have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
      simp [pow_three, pow_two, hf, hg]
    _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
      simpa using (ModularFormClass.qExpansion_sub (h := (1 : ℝ)) (hh := by norm_num)
        (hΓ := by simp) (f := E4.mul (E4.mul E4)) (g := E6.mul E6))
    _ = _ := by
      have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
      have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
      simp [pow_three, pow_two, hf, hg]

/-- Coefficient of `Delta` at `q^6` used to compute `q / Delta`. -/
private lemma Delta_exp_six_local : (qExpansion 1 Delta).coeff 6 = -6048 := by
  have hDeltaaux6 := congrArg (PowerSeries.coeff 6) Deltaaux
  calc
    (qExpansion 1 Delta).coeff 6 =
        ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 6 := by
      simpa using hDeltaaux6
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 6 := by
      simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 6 - (qExpansion 1 (E6 ^ 2)).coeff 6) := by
      rw [qExpansion_E4_E6_sub_local]
      simp
    _ = (1 / 1728 : ℂ) * (34413301440 - 34423752384) := by
      rw [E4_cubed_coeff_six_local, E6_squared_coeff_six_local]
    _ = -6048 := by norm_num

/-- Coefficient of `Delta` at `q^7` used to compute `q / Delta`. -/
private lemma Delta_exp_seven_local : (qExpansion 1 Delta).coeff 7 = -16744 := by
  have hDeltaaux7 := congrArg (PowerSeries.coeff 7) Deltaaux
  calc
    (qExpansion 1 Delta).coeff 7 =
        ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 7 := by
      simpa using hDeltaaux7
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 7 := by
      simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 7 - (qExpansion 1 (E6 ^ 2)).coeff 7) := by
      rw [qExpansion_E4_E6_sub_local]
      simp
    _ = (1 / 1728 : ℂ) * (187477879680 - 187506813312) := by
      rw [E4_cubed_coeff_seven_local, E6_squared_coeff_seven_local]
    _ = -16744 := by norm_num

/-- Constant coefficient of `Delta / q` in the local inverse computation. -/
private lemma Deltaoverq_coeff_zero_local : (qExpansion 1 Deltaoverq).coeff 0 = 1 := by
  simp [qExpansion_coeff, cuspFunction_Deltaoverq_zero]

/-- Coefficient of `Delta / q` at `q^1` in the local inverse computation. -/
private lemma Deltaoverq_coeff_one_local : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 1 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 2 := by simpa using InfSumDeltashift_coeff_eq 1
    _ = -24 := Delta_exp_two

/-- Coefficient of `Delta / q` at `q^2` in the local inverse computation. -/
private lemma Deltaoverq_coeff_two_local : (qExpansion 1 Deltaoverq).coeff 2 = 252 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 2 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 3 := by simpa using InfSumDeltashift_coeff_eq 2
    _ = 252 := Delta_exp_three

/-- Coefficient of `Delta / q` at `q^3` in the local inverse computation. -/
private lemma Deltaoverq_coeff_three_local :
    (qExpansion 1 Deltaoverq).coeff 3 = -1472 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 3 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 4 := by simpa using InfSumDeltashift_coeff_eq 3
    _ = -1472 := Delta_exp_four

/-- Coefficient of `Delta / q` at `q^4` in the local inverse computation. -/
private lemma Deltaoverq_coeff_four_local : (qExpansion 1 Deltaoverq).coeff 4 = 4830 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 4 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 5 := by simpa using InfSumDeltashift_coeff_eq 4
    _ = 4830 := Delta_exp_five

/-- Coefficient of `Delta / q` at `q^5` in the local inverse computation. -/
private lemma Deltaoverq_coeff_five_local :
    (qExpansion 1 Deltaoverq).coeff 5 = -6048 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 5 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 6 := by simpa using InfSumDeltashift_coeff_eq 5
    _ = -6048 := Delta_exp_six_local

/-- Coefficient of `Delta / q` at `q^6` in the local inverse computation. -/
private lemma Deltaoverq_coeff_six_local :
    (qExpansion 1 Deltaoverq).coeff 6 = -16744 := by
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift InfSumDeltashift_eq_Deltaoverq.symm
  calc
    _ = (qExpansion 1 InfSumDeltashift).coeff 6 := by simp [hq]
    _ = (qExpansion 1 Delta).coeff 7 := by simpa using InfSumDeltashift_coeff_eq 6
    _ = -16744 := Delta_exp_seven_local

/-- Map integral `Delta / q` coefficients to complex coefficients for inversion. -/
private lemma integralDeltaoverq_map_coeff_local (n : ℕ) :
    ((powerSeriesMapAlgHom ℤ ℂ) integralDeltaoverq).coeff n =
      (qExpansion 1 Deltaoverq).coeff n := by
  simpa [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
    congrArg (PowerSeries.coeff n) coeTo_of_integralDeltaoverq

/-- Constant coefficient of `q / Delta` in the local inverse computation. -/
private lemma qoverDelta_coeff_zero_local : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
  simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]

/-- Coefficient of `q / Delta` at `q^1` in the local inverse computation. -/
private lemma qoverDelta_coeff_one_local : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
  have hcoeff := congrArg (PowerSeries.coeff 1) integralDeltaoverq_mul_qoverDelta_qExpansion
  have hadd' : (-24 : ℂ) + (qExpansion 1 qoverDelta).coeff 1 = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_one, integralDeltaoverq_map_coeff_local,
      Deltaoverq_coeff_zero_local, Deltaoverq_coeff_one_local, qoverDelta_coeff_zero_local]
      using hcoeff
  have hadd : (qExpansion 1 qoverDelta).coeff 1 + (-24 : ℂ) = 0 := by
    simpa [add_comm] using hadd'
  have hneg : (qExpansion 1 qoverDelta).coeff 1 = -(-24 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Coefficient of `q / Delta` at `q^2` in the local inverse computation. -/
private lemma qoverDelta_coeff_two_local : (qExpansion 1 qoverDelta).coeff 2 = 324 := by
  have hcoeff := congrArg (PowerSeries.coeff 2) integralDeltaoverq_mul_qoverDelta_qExpansion
  have h2eq : (qExpansion 1 qoverDelta).coeff 2
      + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 1 + (252 : ℂ) = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_two_local, integralDeltaoverq_map_coeff_local,
      Deltaoverq_coeff_zero_local, Deltaoverq_coeff_one_local, Deltaoverq_coeff_two_local,
      qoverDelta_coeff_zero_local, add_assoc, add_comm, add_left_comm, mul_comm,
      mul_left_comm, mul_assoc] using hcoeff
  rw [qoverDelta_coeff_one_local] at h2eq
  have hadd : (qExpansion 1 qoverDelta).coeff 2 + (-324 : ℂ) = 0 := by
    have h2eq' := h2eq
    ring_nf at h2eq'
    simpa [add_comm] using h2eq'
  have hneg : (qExpansion 1 qoverDelta).coeff 2 = -(-324 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Coefficient of `q / Delta` at `q^3` in the local inverse computation. -/
private lemma qoverDelta_coeff_three_local :
    (qExpansion 1 qoverDelta).coeff 3 = 3200 := by
  have hcoeff := congrArg (PowerSeries.coeff 3) integralDeltaoverq_mul_qoverDelta_qExpansion
  have h3eq : (qExpansion 1 qoverDelta).coeff 3
      + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
      + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 1 + (-1472 : ℂ) = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_three_local,
      integralDeltaoverq_map_coeff_local, Deltaoverq_coeff_zero_local,
      Deltaoverq_coeff_one_local, Deltaoverq_coeff_two_local,
      Deltaoverq_coeff_three_local, qoverDelta_coeff_zero_local, add_assoc, add_comm,
      add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff
  rw [qoverDelta_coeff_one_local, qoverDelta_coeff_two_local] at h3eq
  have hadd : (qExpansion 1 qoverDelta).coeff 3 + (-3200 : ℂ) = 0 := by
    have h3eq' := h3eq
    ring_nf at h3eq'
    simpa [add_comm] using h3eq'
  have hneg : (qExpansion 1 qoverDelta).coeff 3 = -(-3200 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Coefficient of `q / Delta` at `q^4` in the local inverse computation. -/
private lemma qoverDelta_coeff_four_local :
    (qExpansion 1 qoverDelta).coeff 4 = 25650 := by
  have hcoeff := congrArg (PowerSeries.coeff 4) integralDeltaoverq_mul_qoverDelta_qExpansion
  have h4eq : (qExpansion 1 qoverDelta).coeff 4
      + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 3
      + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
      + (-1472 : ℂ) * (qExpansion 1 qoverDelta).coeff 1 + (4830 : ℂ) = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_four_local,
      integralDeltaoverq_map_coeff_local, Deltaoverq_coeff_zero_local,
      Deltaoverq_coeff_one_local, Deltaoverq_coeff_two_local,
      Deltaoverq_coeff_three_local, Deltaoverq_coeff_four_local, qoverDelta_coeff_zero_local,
      add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff
  rw [qoverDelta_coeff_one_local, qoverDelta_coeff_two_local, qoverDelta_coeff_three_local]
    at h4eq
  have hadd : (qExpansion 1 qoverDelta).coeff 4 + (-25650 : ℂ) = 0 := by
    have h4eq' := h4eq
    ring_nf at h4eq'
    simpa [add_comm] using h4eq'
  have hneg : (qExpansion 1 qoverDelta).coeff 4 = -(-25650 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Coefficient of `q / Delta` at `q^5` in the local inverse computation. -/
private lemma qoverDelta_coeff_five_local :
    (qExpansion 1 qoverDelta).coeff 5 = 176256 := by
  have hcoeff := congrArg (PowerSeries.coeff 5) integralDeltaoverq_mul_qoverDelta_qExpansion
  have h5eq : (qExpansion 1 qoverDelta).coeff 5
      + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 4
      + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 3
      + (-1472 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
      + (4830 : ℂ) * (qExpansion 1 qoverDelta).coeff 1 + (-6048 : ℂ) = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_five, integralDeltaoverq_map_coeff_local,
      Deltaoverq_coeff_zero_local, Deltaoverq_coeff_one_local, Deltaoverq_coeff_two_local,
      Deltaoverq_coeff_three_local, Deltaoverq_coeff_four_local, Deltaoverq_coeff_five_local,
      qoverDelta_coeff_zero_local, add_assoc, add_comm, add_left_comm, mul_comm,
      mul_left_comm, mul_assoc] using hcoeff
  rw [qoverDelta_coeff_one_local, qoverDelta_coeff_two_local, qoverDelta_coeff_three_local,
    qoverDelta_coeff_four_local] at h5eq
  have hadd : (qExpansion 1 qoverDelta).coeff 5 + (-176256 : ℂ) = 0 := by
    have h5eq' := h5eq
    ring_nf at h5eq'
    simpa [add_comm] using h5eq'
  have hneg : (qExpansion 1 qoverDelta).coeff 5 = -(-176256 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Coefficient of `q / Delta` at `q^6` in the local inverse computation. -/
private lemma qoverDelta_coeff_six_local :
    (qExpansion 1 qoverDelta).coeff 6 = 1073720 := by
  have hcoeff := congrArg (PowerSeries.coeff 6) integralDeltaoverq_mul_qoverDelta_qExpansion
  have h6eq : (qExpansion 1 qoverDelta).coeff 6
      + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 5
      + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 4
      + (-1472 : ℂ) * (qExpansion 1 qoverDelta).coeff 3
      + (4830 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
      + (-6048 : ℂ) * (qExpansion 1 qoverDelta).coeff 1 + (-16744 : ℂ) = 0 := by
    simpa [PowerSeries.coeff_mul, antidiagonal_six_local,
      integralDeltaoverq_map_coeff_local, Deltaoverq_coeff_zero_local,
      Deltaoverq_coeff_one_local, Deltaoverq_coeff_two_local,
      Deltaoverq_coeff_three_local, Deltaoverq_coeff_four_local,
      Deltaoverq_coeff_five_local, Deltaoverq_coeff_six_local,
      qoverDelta_coeff_zero_local, add_assoc, add_comm, add_left_comm, mul_comm,
      mul_left_comm, mul_assoc] using hcoeff
  rw [qoverDelta_coeff_one_local, qoverDelta_coeff_two_local, qoverDelta_coeff_three_local,
    qoverDelta_coeff_four_local, qoverDelta_coeff_five_local] at h6eq
  have hadd : (qExpansion 1 qoverDelta).coeff 6 + (-1073720 : ℂ) = 0 := by
    have h6eq' := h6eq
    ring_nf at h6eq'
    simpa [add_comm] using h6eq'
  have hneg : (qExpansion 1 qoverDelta).coeff 6 = -(-1073720 : ℂ) :=
    (eq_neg_iff_add_eq_zero).2 hadd
  simpa using hneg

/-- Local q-expansion coefficient of `qj`, needed for the level-`2` `Y` coefficient. -/
theorem qj_exp_five_local : (qExpansion 1 qj).coeff 5 = 20245856256 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) =
        qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  calc
    _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 5 := by rw [hqj]
    _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 5 := by rw [hmul]
    _ =
        (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 5
          + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 4
          + (qExpansion 1 (E4 ^ 3)).coeff 2 * (qExpansion 1 qoverDelta).coeff 3
          + (qExpansion 1 (E4 ^ 3)).coeff 3 * (qExpansion 1 qoverDelta).coeff 2
          + (qExpansion 1 (E4 ^ 3)).coeff 4 * (qExpansion 1 qoverDelta).coeff 1
          + (qExpansion 1 (E4 ^ 3)).coeff 5 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, antidiagonal_five]
      simp [add_assoc, add_comm, mul_comm]
    _ = _ := by
      simp only [Nat.cast_ofNat, coeff_zero_eq_constantCoeff, qoverDelta_coeff_five_local,
        qoverDelta_coeff_four_local, qoverDelta_coeff_three_local, qoverDelta_coeff_two_local,
        qoverDelta_coeff_one_local, qoverDelta_coeff_zero_local, mul_one]
      rw [E4_cubed_constantCoeff_local, E4_cubed_coeff_one_local,
        E4_cubed_coeff_two_local, E4_cubed_coeff_three_local,
        E4_cubed_coeff_four_local, E4_cubed_coeff_five_local]
      norm_num

/-- Local q-expansion coefficient of `qj`, needed for the level-`2` constant term. -/
theorem qj_exp_six_local : (qExpansion 1 qj).coeff 6 = 333202640600 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) =
        qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  calc
    _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 6 := by rw [hqj]
    _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 6 := by rw [hmul]
    _ =
        (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 6
          + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 5
          + (qExpansion 1 (E4 ^ 3)).coeff 2 * (qExpansion 1 qoverDelta).coeff 4
          + (qExpansion 1 (E4 ^ 3)).coeff 3 * (qExpansion 1 qoverDelta).coeff 3
          + (qExpansion 1 (E4 ^ 3)).coeff 4 * (qExpansion 1 qoverDelta).coeff 2
          + (qExpansion 1 (E4 ^ 3)).coeff 5 * (qExpansion 1 qoverDelta).coeff 1
          + (qExpansion 1 (E4 ^ 3)).coeff 6 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, antidiagonal_six_local]
      simp [add_assoc, add_comm, mul_comm]
    _ = _ := by
      simp only [Nat.cast_ofNat, coeff_zero_eq_constantCoeff, qoverDelta_coeff_six_local,
        qoverDelta_coeff_five_local, qoverDelta_coeff_four_local, qoverDelta_coeff_three_local,
        qoverDelta_coeff_two_local, qoverDelta_coeff_one_local, qoverDelta_coeff_zero_local,
        mul_one]
      rw [E4_cubed_constantCoeff_local, E4_cubed_coeff_one_local,
        E4_cubed_coeff_two_local, E4_cubed_coeff_three_local,
        E4_cubed_coeff_four_local, E4_cubed_coeff_five_local,
        E4_cubed_coeff_six_local]
      norm_num


/-- A Taylor remainder principle for the cusp function of `qj`: once the first
`n` q-expansion terms are identified by a partial sum, the remainder divided by
`q^k` tends to zero whenever `k < n`. -/
private theorem qj_cuspFunction_remainder_tendsto_zero_of_partialSum
    {k n : ℕ} (hkn : k < n) (P : ℂ → ℂ)
    (hpartial :
      (fun q : ℂ =>
        (qExpansionFormalMultilinearSeries (h := 1) (f := qj)).partialSum n q) = P)
    (hP0 : P 0 = cuspFunction 1 qj 0) :
    Tendsto (fun q : ℂ => (cuspFunction 1 qj q - P q) / q ^ k)
      (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds 0) := by
  let p := qExpansionFormalMultilinearSeries (h := 1) (f := qj)
  have hfps : HasFPowerSeriesAt (cuspFunction 1 qj) p (0 : ℂ) := by
    simpa [p] using
      (UpperHalfPlane.hasFPowerSeries_cuspFunction (h := 1) (f := qj)
        (c := fun m : ℕ => (qExpansion 1 qj).coeff m) (by norm_num)
        qj_cuspFunction_AnalyticAt
        (fun τ : ℍ => hasSum_qExpansion_qj (τ := τ))).hasFPowerSeriesAt
  have hOₙ :
      (fun q : ℂ => cuspFunction 1 qj (0 + q) - p.partialSum n q)
        =O[nhds (0 : ℂ)] fun q : ℂ => ‖q‖ ^ n :=
    hfps.isBigO_sub_partialSum_pow n
  have hO :
      (fun q : ℂ => cuspFunction 1 qj q - P q)
        =O[nhds (0 : ℂ)] fun q : ℂ => ‖q‖ ^ n := by
    exact hOₙ.congr_left fun q => by simp [p, hpartial]
  have hsmall_norm :
      (fun q : ℂ => cuspFunction 1 qj q - P q)
        =o[nhds (0 : ℂ)] fun q : ℂ => ‖q‖ ^ k :=
    hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_norm_pow hkn)
  have hsmall_norm' :
      (fun q : ℂ => cuspFunction 1 qj q - P q)
        =o[nhds (0 : ℂ)] fun q : ℂ => ‖q ^ k‖ := by
    simpa [norm_pow] using hsmall_norm
  have hsmall :
      (fun q : ℂ => cuspFunction 1 qj q - P q)
        =o[nhds (0 : ℂ)] fun q : ℂ => q ^ k :=
    Asymptotics.isLittleO_norm_right.mp hsmall_norm'
  have hzero : ∀ q : ℂ, q ^ k = 0 → cuspFunction 1 qj q - P q = 0 := by
    intro q hq
    have hq0 : q = 0 := eq_zero_of_pow_eq_zero hq
    subst q
    rw [hP0]
    simp
  have htendsto :
      Tendsto (fun q : ℂ => (cuspFunction 1 qj q - P q) / q ^ k)
        (nhds (0 : ℂ)) (nhds 0) := by
    rwa [Asymptotics.isLittleO_iff_tendsto hzero] at hsmall
  exact htendsto.mono_left nhdsWithin_le_nhds

/-- Taylor-remainder estimate for the first three terms of the cusp function of `qj`. -/
private theorem qj_cuspFunction_three_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) qj q - (1 + 744 * q + 196884 * q ^ 2)) / q ^ 2)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  let P : ℂ → ℂ := fun q => 1 + 744 * q + 196884 * q ^ 2
  have hpartial :
      (fun q : ℂ =>
        (qExpansionFormalMultilinearSeries (h := 1) (f := qj)).partialSum 3 q) = P := by
    funext q
    have h0 : (coeff 0) (qExpansion 1 ⇑qj) = 1 := by
      simpa using qj_exp_zero
    have h1 : (coeff 1) (qExpansion 1 ⇑qj) = 744 := by
      simpa using qj_exp_one
    have h2 : (coeff 2) (qExpansion 1 ⇑qj) = 196884 := by
      simpa using qj_exp_two
    simp only [FormalMultilinearSeries.partialSum, qExpansionFormalMultilinearSeries,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, P]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [h0, h1, h2]
    ring_nf
  have hP0 : P 0 = cuspFunction 1 qj 0 := by
    have hqj0 : cuspFunction 1 qj 0 = 1 := by
      simpa [qExpansion_coeff] using qj_exp_zero
    simp [P, hqj0]
  simpa [P] using
    qj_cuspFunction_remainder_tendsto_zero_of_partialSum
      (k := 2) (n := 3) (by norm_num) P hpartial hP0

/-- Laurent-remainder estimate for `j` after keeping terms through `196884 q`. -/
theorem j_cuspFunction_three_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) j q - (q⁻¹ + 744 + 196884 * q)) / q)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEqJ :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q : ℂ =>
        q⁻¹ * cuspFunction 1 qj q := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
        (h := 1) (hh := by norm_num) (f := j))
  have hEq :
      (fun q : ℂ =>
        (cuspFunction 1 j q - (q⁻¹ + 744 + 196884 * q)) / q) =ᶠ[
          nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
        (cuspFunction 1 qj q - (1 + 744 * q + 196884 * q ^ 2)) / q ^ 2 := by
    filter_upwards [hEqJ, self_mem_nhdsWithin] with q hJ hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    rw [hJ]
    field_simp [hq0]
  exact qj_cuspFunction_three_term_remainder.congr' hEq.symm

/-- Taylor-remainder estimate for `qj` after keeping terms through `q^5`. -/
private theorem qj_cuspFunction_six_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) qj q -
          (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
            864299970 * q ^ 4 + 20245856256 * q ^ 5)) / q ^ 5)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  let P : ℂ → ℂ := fun q =>
    1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
      864299970 * q ^ 4 + 20245856256 * q ^ 5
  have hpartial :
      (fun q : ℂ =>
        (qExpansionFormalMultilinearSeries (h := 1) (f := qj)).partialSum 6 q) = P := by
    funext q
    have h0 : (coeff 0) (qExpansion 1 ⇑qj) = 1 := by
      simpa using qj_exp_zero
    have h1 : (coeff 1) (qExpansion 1 ⇑qj) = 744 := by
      simpa using qj_exp_one
    have h2 : (coeff 2) (qExpansion 1 ⇑qj) = 196884 := by
      simpa using qj_exp_two
    have h3 : (coeff 3) (qExpansion 1 ⇑qj) = 21493760 := by
      simpa using qj_exp_three
    have h4 : (coeff 4) (qExpansion 1 ⇑qj) = 864299970 := by
      simpa using qj_exp_four
    have h5 : (coeff 5) (qExpansion 1 ⇑qj) = 20245856256 := by
      simpa using qj_exp_five_local
    simp only [FormalMultilinearSeries.partialSum, qExpansionFormalMultilinearSeries,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, P]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [h0, h1, h2, h3, h4, h5]
    ring_nf
  have hP0 : P 0 = cuspFunction 1 qj 0 := by
    have hqj0 : cuspFunction 1 qj 0 = 1 := by
      simpa [qExpansion_coeff] using qj_exp_zero
    simp [P, hqj0]
  simpa [P] using
    qj_cuspFunction_remainder_tendsto_zero_of_partialSum
      (k := 5) (n := 6) (by norm_num) P hpartial hP0

/-- Laurent-remainder estimate for `j` after keeping terms through the `q^4` term. -/
theorem j_cuspFunction_five_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) j q -
          (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
            864299970 * q ^ 3 + 20245856256 * q ^ 4)) / q ^ 4)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEqJ :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q : ℂ =>
        q⁻¹ * cuspFunction 1 qj q := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
        (h := 1) (hh := by norm_num) (f := j))
  have hEq :
      (fun q : ℂ =>
        (cuspFunction 1 j q -
          (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
            864299970 * q ^ 3 + 20245856256 * q ^ 4)) / q ^ 4) =ᶠ[
          nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
          (cuspFunction 1 qj q -
            (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
              864299970 * q ^ 4 + 20245856256 * q ^ 5)) / q ^ 5 := by
    filter_upwards [hEqJ, self_mem_nhdsWithin] with q hJ hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    rw [hJ]
    field_simp [hq0]
  exact qj_cuspFunction_six_term_remainder.congr' hEq.symm

/-- Taylor-remainder estimate for `qj` after keeping terms through `q^6`. -/
private theorem qj_cuspFunction_seven_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) qj q -
          (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
            864299970 * q ^ 4 + 20245856256 * q ^ 5 +
              333202640600 * q ^ 6)) / q ^ 6)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  let P : ℂ → ℂ := fun q =>
    1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
      864299970 * q ^ 4 + 20245856256 * q ^ 5 +
        333202640600 * q ^ 6
  have hpartial :
      (fun q : ℂ =>
        (qExpansionFormalMultilinearSeries (h := 1) (f := qj)).partialSum 7 q) = P := by
    funext q
    have h0 : (coeff 0) (qExpansion 1 ⇑qj) = 1 := by
      simpa using qj_exp_zero
    have h1 : (coeff 1) (qExpansion 1 ⇑qj) = 744 := by
      simpa using qj_exp_one
    have h2 : (coeff 2) (qExpansion 1 ⇑qj) = 196884 := by
      simpa using qj_exp_two
    have h3 : (coeff 3) (qExpansion 1 ⇑qj) = 21493760 := by
      simpa using qj_exp_three
    have h4 : (coeff 4) (qExpansion 1 ⇑qj) = 864299970 := by
      simpa using qj_exp_four
    have h5 : (coeff 5) (qExpansion 1 ⇑qj) = 20245856256 := by
      simpa using qj_exp_five_local
    have h6 : (coeff 6) (qExpansion 1 ⇑qj) = 333202640600 := by
      simpa using qj_exp_six_local
    simp only [FormalMultilinearSeries.partialSum, qExpansionFormalMultilinearSeries,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, P]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    rw [h0, h1, h2, h3, h4, h5, h6]
    ring_nf
  have hP0 : P 0 = cuspFunction 1 qj 0 := by
    have hqj0 : cuspFunction 1 qj 0 = 1 := by
      simpa [qExpansion_coeff] using qj_exp_zero
    simp [P, hqj0]
  simpa [P] using
    qj_cuspFunction_remainder_tendsto_zero_of_partialSum
      (k := 6) (n := 7) (by norm_num) P hpartial hP0

/-- Laurent-remainder estimate for `j` after keeping terms through the `q^5` term. -/
theorem j_cuspFunction_six_term_remainder :
    Tendsto
      (fun q : ℂ =>
        (cuspFunction (1 : ℝ) j q -
          (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
            864299970 * q ^ 3 + 20245856256 * q ^ 4 +
              333202640600 * q ^ 5)) / q ^ 5)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEqJ :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q : ℂ =>
        q⁻¹ * cuspFunction 1 qj q := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
        (h := 1) (hh := by norm_num) (f := j))
  have hEq :
      (fun q : ℂ =>
        (cuspFunction 1 j q -
          (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
            864299970 * q ^ 3 + 20245856256 * q ^ 4 +
              333202640600 * q ^ 5)) / q ^ 5) =ᶠ[
          nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
          (cuspFunction 1 qj q -
            (1 + 744 * q + 196884 * q ^ 2 + 21493760 * q ^ 3 +
              864299970 * q ^ 4 + 20245856256 * q ^ 5 +
                333202640600 * q ^ 6)) / q ^ 6 := by
    filter_upwards [hEqJ, self_mem_nhdsWithin] with q hJ hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    rw [hJ]
    field_simp [hq0]
  exact qj_cuspFunction_seven_term_remainder.congr' hEq.symm

/-- The leading Laurent coefficient of `j` at the cusp is `1`. -/
theorem j_cuspFunction_trailingCoeff :
    meromorphicTrailingCoeffAt (cuspFunction 1 j) (0 : ℂ) = 1 := by
  have hEq :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q =>
        q⁻¹ * cuspFunction 1 qj q := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
        (h := 1) (hh := by norm_num) (f := j))
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE hEq]
  have hid : meromorphicTrailingCoeffAt (id : ℂ → ℂ) (0 : ℂ) = 1 := by
    simpa [id] using
      (meromorphicTrailingCoeffAt_id_sub_const (𝕜 := ℂ) (x := (0 : ℂ)) (y := (0 : ℂ)))
  have hidInv : meromorphicTrailingCoeffAt (id⁻¹ : ℂ → ℂ) (0 : ℂ) = 1 := by
    simpa [hid] using
      (meromorphicTrailingCoeffAt_inv (𝕜 := ℂ) (f := id) (x := (0 : ℂ)))
  have hqj : meromorphicTrailingCoeffAt (cuspFunction 1 qj) (0 : ℂ) = 1 := by
    have hqj0 : cuspFunction 1 qj 0 = 1 := by
      simpa [qExpansion_coeff] using qj_exp_zero
    simpa [hqj0] using
      qj_cuspFunction_AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by simp [hqj0])
  have hmul := ((MeromorphicAt.id (0 : ℂ)).inv).meromorphicTrailingCoeffAt_mul
    qj_cuspFunction_AnalyticAt.meromorphicAt
  simpa [Pi.mul_apply, hidInv, hqj] using hmul

/-- The cusp function of `j` has meromorphic order `-1` at the cusp. -/
private lemma j_cuspFunction_order :
    meromorphicOrderAt (cuspFunction 1 j) (0 : ℂ) = (-1 : ℤ) := by
  have h0 : poleOrder 1 j ≠ 0 := by simp [j_poleOrder]
  simpa [j_poleOrder] using
    (meromorphicOrderAt_cuspFunction_eq_neg_poleOrder (h := 1) (f := j) h0)

/-- On a punctured cusp neighbourhood, `j^r` becomes the `r`-th power of
the cusp function of `j`. -/
private lemma polynomialInJ_X_pow_cusp_eventuallyEq (r : ℕ) :
    (cuspFunction 1 j) ^ r =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      cuspFunction 1 (polynomialInJ (Polynomial.X ^ r)) := by
  simpa [Polynomial.eval_pow, polynomialInJ] using
    polynomialInJ_cuspFunction_eventuallyEq (Polynomial.X ^ r)

/-- The leading Laurent coefficient of `j^r` at the cusp is `1`. -/
theorem polynomialInJ_X_pow_cusp_trailingCoeff (r : ℕ) :
    meromorphicTrailingCoeffAt
      (cuspFunction 1 (polynomialInJ (Polynomial.X ^ r))) (0 : ℂ) = 1 := by
  have hEq := polynomialInJ_X_pow_cusp_eventuallyEq r
  rw [← meromorphicTrailingCoeffAt_congr_nhdsNE hEq]
  rw [j_cuspFunction_Meromorphic.meromorphicTrailingCoeffAt_pow]
  simp [j_cuspFunction_trailingCoeff]

/-- The cusp order of `j^r` is `-r`. -/
theorem polynomialInJ_X_pow_cusp_order (r : ℕ) :
    meromorphicOrderAt (cuspFunction 1 (polynomialInJ (Polynomial.X ^ r))) (0 : ℂ) =
      (-(r : ℤ) : WithTop ℤ) := by
  have hEq := polynomialInJ_X_pow_cusp_eventuallyEq r
  rw [← meromorphicOrderAt_congr hEq]
  rw [meromorphicOrderAt_pow j_cuspFunction_Meromorphic]
  rw [j_cuspFunction_order]
  change ((r : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) =
    ((-(r : ℤ) : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul]
  congr
  ring

/-- On a punctured cusp neighbourhood, `a * j^r` becomes `a` times the
`r`-th power of the cusp function of `j`. -/
private lemma polynomialInJ_C_mul_X_pow_cusp_eventuallyEq (a : ℂ) (r : ℕ) :
    (fun q : ℂ => a * (cuspFunction 1 j q) ^ r)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        cuspFunction 1 (polynomialInJ (Polynomial.C a * Polynomial.X ^ r)) := by
  filter_upwards [polynomialInJ_cuspFunction_eventuallyEq
    (Polynomial.C a * Polynomial.X ^ r)] with q hq
  rw [← hq]
  simp [Polynomial.eval_mul, Polynomial.eval_pow]

/-- The leading Laurent coefficient of `a * j^r` at the cusp is `a`. -/
theorem polynomialInJ_C_mul_X_pow_cusp_trailingCoeff (a : ℂ) (r : ℕ) :
    meromorphicTrailingCoeffAt
      (cuspFunction 1 (polynomialInJ (Polynomial.C a * Polynomial.X ^ r))) (0 : ℂ) =
        a := by
  have hEq := polynomialInJ_C_mul_X_pow_cusp_eventuallyEq a r
  rw [← meromorphicTrailingCoeffAt_congr_nhdsNE hEq]
  have hconst : MeromorphicAt (fun _ : ℂ => a) (0 : ℂ) := MeromorphicAt.const a 0
  have hpow : MeromorphicAt ((cuspFunction 1 j) ^ r) (0 : ℂ) :=
    j_cuspFunction_Meromorphic.pow r
  change meromorphicTrailingCoeffAt ((fun _ : ℂ => a) * ((cuspFunction 1 j) ^ r))
      (0 : ℂ) = a
  rw [hconst.meromorphicTrailingCoeffAt_mul hpow]
  rw [j_cuspFunction_Meromorphic.meromorphicTrailingCoeffAt_pow]
  simp [meromorphicTrailingCoeffAt_const, j_cuspFunction_trailingCoeff]

/-- If `a ≠ 0`, the cusp order of `a * j^r` is `-r`. -/
theorem polynomialInJ_C_mul_X_pow_cusp_order {a : ℂ} (ha : a ≠ 0) (r : ℕ) :
    meromorphicOrderAt
      (cuspFunction 1 (polynomialInJ (Polynomial.C a * Polynomial.X ^ r))) (0 : ℂ) =
        (-(r : ℤ) : WithTop ℤ) := by
  have hEq := polynomialInJ_C_mul_X_pow_cusp_eventuallyEq a r
  rw [← meromorphicOrderAt_congr hEq]
  change meromorphicOrderAt ((fun _ : ℂ => a) * ((cuspFunction 1 j) ^ r)) (0 : ℂ) =
    (-(r : ℤ) : WithTop ℤ)
  rw [meromorphicOrderAt_mul_of_ne_zero (g := fun _ : ℂ => a)
    (f := (cuspFunction 1 j) ^ r) analyticAt_const (by simpa using ha)]
  rw [meromorphicOrderAt_pow j_cuspFunction_Meromorphic]
  rw [j_cuspFunction_order]
  change ((r : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) =
    ((-(r : ℤ) : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul]
  congr
  ring

/-- The cusp function of evaluating a polynomial in a meromorphic function is meromorphic. -/
private lemma polynomialInJ_cuspEval_Meromorphic (P : Polynomial ℂ) :
    MeromorphicAt (fun q : ℂ => P.eval (cuspFunction 1 j q)) 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext q
      simp
  | monomial n a =>
      simpa using (MeromorphicAt.const a (0 : ℂ)).mul (j_cuspFunction_Meromorphic.pow n)

/-- The cusp function of any `P(j)` is meromorphic at `0`, as used in Cox
Lemma 11.10(ii). -/
theorem polynomialInJ_cuspFunction_Meromorphic (P : Polynomial ℂ) :
    MeromorphicAt (cuspFunction 1 (polynomialInJ P)) 0 :=
  (polynomialInJ_cuspEval_Meromorphic P).congr
    (polynomialInJ_cuspFunction_eventuallyEq P)

/-- At the level-one cusp, cusp functions commute with subtraction on a punctured
neighbourhood. -/
private lemma cuspFunction_sub_eventuallyEq_one (f g : ℍ → ℂ) :
    (fun q : ℂ => cuspFunction 1 f q - cuspFunction 1 g q)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] cuspFunction 1 (f - g) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hf :
      cuspFunction 1 f q =
        f (UpperHalfPlane.ofComplex (Periodic.invQParam 1 q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero (1 : ℝ)
        (f ∘ UpperHalfPlane.ofComplex) hq0)
  have hg :
      cuspFunction 1 g q =
        g (UpperHalfPlane.ofComplex (Periodic.invQParam 1 q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero (1 : ℝ)
        (g ∘ UpperHalfPlane.ofComplex) hq0)
  have hsub :
      cuspFunction 1 (f - g) q =
        (f - g) (UpperHalfPlane.ofComplex (Periodic.invQParam 1 q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero (1 : ℝ)
        ((f - g) ∘ UpperHalfPlane.ofComplex) hq0)
  rw [hf, hg, hsub]
  rfl

/-- Meromorphicity at the level-one cusp is closed under subtracting plain functions. -/
theorem cuspFunction_sub_Meromorphic_one {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction 1 f) 0)
    (hg : MeromorphicAt (cuspFunction 1 g) 0) :
    MeromorphicAt (cuspFunction 1 (f - g)) 0 :=
  (hf.sub hg).congr (cuspFunction_sub_eventuallyEq_one f g)

/-- If two meromorphic germs have the same order and leading coefficient, their
difference has higher order. -/
private lemma meromorphicOrderAt_sub_gt_of_same_order_trailingCoeff
    {f g : ℂ → ℂ} (hf : MeromorphicAt f (0 : ℂ)) (hg : MeromorphicAt g (0 : ℂ))
    {n : ℤ} (hf_order : meromorphicOrderAt f (0 : ℂ) = (n : WithTop ℤ))
    (hg_order : meromorphicOrderAt g (0 : ℂ) = (n : WithTop ℤ))
    (htrail :
      meromorphicTrailingCoeffAt f (0 : ℂ) = meromorphicTrailingCoeffAt g (0 : ℂ)) :
    (n : WithTop ℤ) < meromorphicOrderAt (f - g) (0 : ℂ) := by
  obtain ⟨F, hFan, hF0, hF_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hf_order
  obtain ⟨G, hGan, hG0, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hg_order
  have hFtrail : meromorphicTrailingCoeffAt f (0 : ℂ) = F 0 := by
    exact hFan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hF0 hF_eq
  have hGtrail : meromorphicTrailingCoeffAt g (0 : ℂ) = G 0 := by
    exact hGan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hG0 hG_eq
  have hFG0 : (F - G) 0 = 0 := by
    rw [Pi.sub_apply, sub_eq_zero]
    exact hFtrail ▸ hGtrail ▸ htrail
  have hEq :
      (f - g) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun z : ℂ => (z - 0) ^ n * (F - G) z := by
    filter_upwards [hF_eq, hG_eq] with z hfz hgz
    rw [Pi.sub_apply, hfz, hgz]
    simp only [smul_eq_mul]
    change (z - 0) ^ n * F z - (z - 0) ^ n * G z =
      (z - 0) ^ n * (F z - G z)
    rw [mul_sub]
  rw [meromorphicOrderAt_congr hEq]
  change (n : WithTop ℤ) <
    meromorphicOrderAt ((fun z : ℂ => (z - 0) ^ n) * (F - G)) (0 : ℂ)
  have hpow_mer : MeromorphicAt (fun z : ℂ => (z - 0) ^ n) (0 : ℂ) := by
    fun_prop
  have hFGan : AnalyticAt ℂ (F - G) 0 := hFan.sub hGan
  rw [meromorphicOrderAt_mul hpow_mer hFGan.meromorphicAt]
  have hpow_order :
      meromorphicOrderAt (fun z : ℂ => (z - 0) ^ n) (0 : ℂ) = (n : WithTop ℤ) := by
    simpa using (meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := (0 : ℂ)) (n := n))
  rw [hpow_order]
  have hFGpos : (0 : WithTop ℤ) < meromorphicOrderAt (F - G) (0 : ℂ) := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos hFGan.meromorphicAt).1
    simpa [hFG0] using hFGan.continuousAt.continuousWithinAt.tendsto
  cases hFGorder : meromorphicOrderAt (F - G) (0 : ℂ) with
  | top =>
      simp
  | coe m =>
      have hmpos : 0 < m := by
        have : (0 : WithTop ℤ) < (m : WithTop ℤ) := by
          simpa [hFGorder] using hFGpos
        exact_mod_cast this
      change (n : WithTop ℤ) < ((n + m : ℤ) : WithTop ℤ)
      exact_mod_cast (lt_add_of_pos_right n hmpos)

/-- A strict improvement of meromorphic order past `-M` lowers the pole order below `M`. -/
private lemma poleOrder_lt_of_meromorphicOrderAt_gt_neg {f : ℍ → ℂ} {M : ℕ}
    (hM : M ≠ 0)
    (hgt : (-(M : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (cuspFunction 1 f) (0 : ℂ)) :
    poleOrder 1 f < M := by
  unfold UpperHalfPlane.poleOrder
  cases ho : meromorphicOrderAt (cuspFunction 1 f) (0 : ℂ) with
  | top =>
      simp [Nat.pos_of_ne_zero hM]
  | coe k =>
      by_cases hk : k < 0
      · have hgt_int : -(M : ℤ) < k := by
          have hgt' : ((-(M : ℤ) : ℤ) : WithTop ℤ) < (k : WithTop ℤ) := by
            simpa [ho] using hgt
          exact_mod_cast hgt'
        have hk_le : k ≤ 0 := le_of_lt hk
        have hnatAbs : ((Int.natAbs k : ℕ) : ℤ) = -k :=
          Int.ofNat_natAbs_of_nonpos hk_le
        rw [if_pos (by simpa [ho] using hk)]
        rw [WithTop.untopD_coe]
        have hnatAbs_lt : (k.natAbs : ℤ) < (M : ℤ) := by
          rw [hnatAbs]
          linarith
        exact_mod_cast hnatAbs_lt
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        rw [if_neg (by
          have : ¬ ((k : WithTop ℤ) < 0) := by exact_mod_cast hk
          simpa [ho] using this)]
        exact hMpos

/-- A nonzero pole order gives a nonzero trailing coefficient of the cusp function. -/
private lemma meromorphicTrailingCoeffAt_cuspFunction_ne_zero_of_poleOrder_ne_zero
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction 1 f) (0 : ℂ))
    (h0 : poleOrder 1 f ≠ 0) :
    meromorphicTrailingCoeffAt (cuspFunction 1 f) (0 : ℂ) ≠ 0 := by
  have horder :
      meromorphicOrderAt (cuspFunction 1 f) (0 : ℂ) =
        (-(poleOrder 1 f : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_cuspFunction_eq_neg_poleOrder (h := 1) (f := f) h0
  exact hmero.meromorphicTrailingCoeffAt_ne_zero (by
    rw [horder]
    simp)

/-- Subtracting the matching leading term `a * j^M` strictly lowers the pole order. -/
private lemma poleOrder_sub_polynomialInJ_leadingTerm_lt {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction 1 f) (0 : ℂ)) (h0 : poleOrder 1 f ≠ 0) :
    poleOrder 1
      (f - polynomialInJ
        (Polynomial.C (meromorphicTrailingCoeffAt (cuspFunction 1 f) (0 : ℂ)) *
          Polynomial.X ^ poleOrder 1 f)) < poleOrder 1 f := by
  let M := poleOrder 1 f
  let a := meromorphicTrailingCoeffAt (cuspFunction 1 f) (0 : ℂ)
  let P : Polynomial ℂ := Polynomial.C a * Polynomial.X ^ M
  have ha : a ≠ 0 := by
    simpa [a] using meromorphicTrailingCoeffAt_cuspFunction_ne_zero_of_poleOrder_ne_zero
      (f := f) hmero h0
  have hf_order :
      meromorphicOrderAt (cuspFunction 1 f) (0 : ℂ) = (-(M : ℤ) : WithTop ℤ) := by
    simpa [M] using meromorphicOrderAt_cuspFunction_eq_neg_poleOrder
      (h := 1) (f := f) h0
  have hP_order :
      meromorphicOrderAt (cuspFunction 1 (polynomialInJ P)) (0 : ℂ) =
        (-(M : ℤ) : WithTop ℤ) := by
    simpa [P] using polynomialInJ_C_mul_X_pow_cusp_order (a := a) ha M
  have htrail :
      meromorphicTrailingCoeffAt (cuspFunction 1 f) (0 : ℂ) =
        meromorphicTrailingCoeffAt (cuspFunction 1 (polynomialInJ P)) (0 : ℂ) := by
    simpa [a, P] using (polynomialInJ_C_mul_X_pow_cusp_trailingCoeff a M).symm
  have hgt :
      (-(M : ℤ) : WithTop ℤ) <
        meromorphicOrderAt
          (cuspFunction 1 f - cuspFunction 1 (polynomialInJ P)) (0 : ℂ) :=
    meromorphicOrderAt_sub_gt_of_same_order_trailingCoeff hmero
      (polynomialInJ_cuspFunction_Meromorphic P) hf_order hP_order htrail
  have hgt_cusp :
      (-(M : ℤ) : WithTop ℤ) <
        meromorphicOrderAt (cuspFunction 1 (f - polynomialInJ P)) (0 : ℂ) := by
    rw [← meromorphicOrderAt_congr (cuspFunction_sub_eventuallyEq_one f (polynomialInJ P))]
    exact hgt
  simpa [M, P] using
    poleOrder_lt_of_meromorphicOrderAt_gt_neg (f := f - polynomialInJ P) h0 hgt_cusp

/-- Principal-part cancellation by `P(j)`, the constructive step in Cox
Lemma 11.10(ii). -/
theorem exists_polynomialInJ_principal_part {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction 1 f) (0 : ℂ)) :
    ∃ P : Polynomial ℂ, poleOrder 1 (f - polynomialInJ P) = 0 := by
  suffices aux :
      ∀ m : ℕ, ∀ f : ℍ → ℂ,
        MeromorphicAt (cuspFunction 1 f) (0 : ℂ) →
        poleOrder 1 f = m →
        ∃ P : Polynomial ℂ, poleOrder 1 (f - polynomialInJ P) = 0 by
    exact aux (poleOrder 1 f) f hmero rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro f hmero hm
      by_cases h0 : poleOrder 1 f = 0
      · refine ⟨0, ?_⟩
        have hfun : f - polynomialInJ 0 = f := by
          funext z
          simp [polynomialInJ]
        simpa [hfun] using h0
      · let a := meromorphicTrailingCoeffAt (cuspFunction 1 f) (0 : ℂ)
        let P0 : Polynomial ℂ := Polynomial.C a * Polynomial.X ^ poleOrder 1 f
        let F : ℍ → ℂ := f - polynomialInJ P0
        have hltF : poleOrder 1 F < m := by
          have hlt := poleOrder_sub_polynomialInJ_leadingTerm_lt
            (f := f) hmero h0
          simpa [F, P0, hm] using hlt
        have hFmero : MeromorphicAt (cuspFunction 1 F) (0 : ℂ) := by
          exact cuspFunction_sub_Meromorphic_one hmero
            (polynomialInJ_cuspFunction_Meromorphic P0)
        obtain ⟨Q, hQ⟩ := ih (poleOrder 1 F) hltF F hFmero rfl
        refine ⟨P0 + Q, ?_⟩
        have hfun : F - polynomialInJ Q = f - polynomialInJ (P0 + Q) := by
          funext z
          simp [F, polynomialInJ]
          ring
        simpa [hfun] using hQ

/-- If the principal part can be cancelled by some `P(j)`, then the level-one
function is a polynomial in `j`. -/
theorem levelOne_meromorphic_polynomialInJ_of_principal_part {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f)
    (hmero : MeromorphicAt (cuspFunction 1 f) 0)
    (hprincipal : ∃ P : Polynomial ℂ, poleOrder 1 (f - polynomialInJ P) = 0) :
    ∃ P : Polynomial ℂ, f = polynomialInJ P := by
  obtain ⟨P, hPpole⟩ := hprincipal
  let F : ℍ → ℂ := f - polynomialInJ P
  have hFslash : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := by
    intro γ
    ext z
    have hfγ := congrFun (hslash γ) z
    have hPγ := congrFun (polynomialInJ_slashInvariant P γ) z
    simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, F, Pi.sub_apply] at hfγ hPγ ⊢
    rw [hfγ, hPγ]
  have hFmdiff : MDiff F := hmdiff.sub (polynomialInJ_MDifferentiable P)
  have hFmero : MeromorphicAt (cuspFunction 1 F) 0 :=
    cuspFunction_sub_Meromorphic_one hmero (polynomialInJ_cuspFunction_Meromorphic P)
  obtain ⟨c, hc⟩ :=
    levelOne_weightZero_constant_of_slash_poleOrder_zero hFslash hFmdiff hFmero hPpole
  refine ⟨P + Polynomial.C c, ?_⟩
  ext z
  have hc_fun := congrFun hc z
  change f z = (P + Polynomial.C c).eval (j z)
  have hc_point : f z - polynomialInJ P z = c := by
    simpa [F, Function.const_apply] using hc_fun
  rw [Polynomial.eval_add, Polynomial.eval_C]
  rw [sub_eq_iff_eq_add] at hc_point
  simpa [polynomialInJ, add_comm] using hc_point

/-- Cox Lemma 11.10(ii), in the holomorphic-on-`ℍ` and meromorphic-at-cusp
setting: a level-one function is a polynomial in `j`. -/
theorem levelOne_meromorphic_polynomialInJ {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f)
    (hmero : MeromorphicAt (cuspFunction 1 f) 0) :
    ∃ P : Polynomial ℂ, f = polynomialInJ P :=
  levelOne_meromorphic_polynomialInJ_of_principal_part hslash hmdiff hmero
    (exists_polynomialInJ_principal_part hmero)

end PolynomialInJ

end modularEquation

end

end Test
