/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import XYin.PhD.Cox.LatticeJ
import XYin.PhD.Cox.ModularFunction.LevelJ

/-!
# Level-one modular functions and Cox Theorem 11.9

The public statements use the bundled `ModularFunction` definition. A holomorphic level-one
modular function is a polynomial in `j`; clearing its poles on a fundamental domain proves
that every level-one modular function is rational in `j`.

The supporting raw-expression API and the bundled level transform `j(Nτ)` are developed in
`ModularFunction.CuspData` and `ModularFunction.LevelJ`.
-/

open Complex Filter Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- Cox Lemma 11.10(i): a level-one modular function holomorphic on `ℍ` and at `∞` is
constant. -/
private theorem levelOne_constant_of_holomorphic {f : ℍ → ℂ}
    (hf : LevelOneCuspData f) (hfH : MDiff f)
    (hf_cusp : AnalyticAt ℂ (cuspFunction 1 f) 0) :
    ∃ c : ℂ, f = fun _ ↦ c := by
  have hfbdd : IsBoundedAtImInfty f :=
    (tendsto_atImInfty_of_continuousAt_cuspFunction one_pos hf.periodic
      hf_cusp.continuousAt).isBigO_one ℝ
  let F : ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 0 :=
    { toFun := f
      slash_action_eq' := by
        rintro _ ⟨γ, rfl⟩
        exact hf.slash_sl2 γ
      holo' := hfH
      bdd_at_cusps' := by
        intro c hc
        rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc]
        obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc
        exact ⟨γ, hγ.symm, by simpa only [hf.slash_sl2 γ] using hfbdd⟩ }
  simpa only [F, Function.const_def] using ModularFormClass.levelOne_weight_zero_const F

private lemma cuspData_sub_const_mul_pow
    (N : ℕ+) {f g : ℍ → ℂ} (hf : CuspData N f)
    (hg : CuspData N g) (a : ℂ) (m : ℕ) :
    CuspData N (fun τ ↦ f τ - a * g τ ^ m) :=
  ⟨fun z hz ↦ (hf.meromorphicAt z hz).fun_sub
      ((MeromorphicAt.const a z).fun_mul ((hg.meromorphicAt z hz).fun_pow m)),
    fun γ ↦ SL_slash_zero_eq_iff.2 fun τ ↦ by simp only [hf.apply_smul, hg.apply_smul],
    fun γ ↦ meromorphicAt_cuspFunction_sub (hf.meromorphicAt_cuspFunction γ)
      (meromorphicAt_cuspFunction_const_mul a
        (meromorphicAt_cuspFunction_pow (hg.meromorphicAt_cuspFunction γ) m))⟩

private lemma meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f g : 𝕜 → 𝕜} {x : 𝕜} {n : ℤ}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
    (hfn : meromorphicOrderAt f x = n) (hgn : meromorphicOrderAt g x = n)
    (htc : meromorphicTrailingCoeffAt f x = meromorphicTrailingCoeffAt g x) :
    (n : WithTop ℤ) < meromorphicOrderAt (fun z ↦ f z - g z) x := by
  obtain ⟨F, hFan, hF0, hFeq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hfn
  obtain ⟨G, hGan, hG0, hGeq⟩ := (meromorphicOrderAt_eq_int_iff hg).mp hgn
  have hFtc : meromorphicTrailingCoeffAt f x = F x :=
    hFan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hF0 hFeq
  have hGtc : meromorphicTrailingCoeffAt g x = G x :=
    hGan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hG0 hGeq
  let H : 𝕜 → 𝕜 := fun z ↦ F z - G z
  have hHan : AnalyticAt 𝕜 H x := hFan.sub hGan
  have hH0 : H x = 0 := by
    rw [show H x = F x - G x from rfl, sub_eq_zero, ← hFtc, ← hGtc]
    exact htc
  have hHne : meromorphicOrderAt H x ≠ 0 := by
    intro h
    exact (hHan.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h) hH0
  have hHpos : 0 < meromorphicOrderAt H x :=
    lt_of_le_of_ne hHan.meromorphicOrderAt_nonneg (Ne.symm hHne)
  have heq : (fun z ↦ f z - g z) =ᶠ[nhdsWithin x ({x}ᶜ)]
      fun z ↦ (z - x) ^ n * H z := by
    filter_upwards [hFeq, hGeq] with z hfz hgz
    simp [hfz, hgz, H, smul_eq_mul, mul_sub]
  rw [meromorphicOrderAt_congr heq]
  change (n : WithTop ℤ) < meromorphicOrderAt (((· - x) ^ n) * H) x
  rw [meromorphicOrderAt_mul (by fun_prop) hHan.meromorphicAt,
    meromorphicOrderAt_zpow_id_sub_const]
  cases ho : meromorphicOrderAt H x with
  | top => simp
  | coe k =>
      have hk : 0 < k := by exact_mod_cast (by simpa [ho] using hHpos)
      simpa [ho, ← WithTop.coe_add] using lt_add_of_pos_right n hk

private lemma exists_const_poleOrder_sub_mul_pow_lt
    {f g : ℍ → ℂ}
    (hfmer : MeromorphicAt (cuspFunction 1 f) 0)
    (hgmer : MeromorphicAt (cuspFunction 1 g) 0)
    (hgorder : poleOrder 1 g = 1) (hm : 0 < poleOrder 1 f) :
    ∃ a : ℂ, poleOrder 1
      (fun τ ↦ f τ - a * g τ ^ poleOrder 1 f) < poleOrder 1 f := by
  set m := poleOrder 1 f
  set G := cuspFunction 1 g
  have hForder : meromorphicOrderAt (cuspFunction 1 f) 0 = -(m : ℤ) :=
    meromorphicOrderAt_cuspFunction_eq_neg_poleOrder hm.ne'
  have hGorder : meromorphicOrderAt G 0 = -(1 : ℤ) := (poleOrder_eq_iff one_ne_zero).1 hgorder
  have hGtc0 := hgmer.meromorphicTrailingCoeffAt_ne_zero (hGorder ▸ WithTop.coe_ne_top)
  let a := meromorphicTrailingCoeffAt (cuspFunction 1 f) 0 / meromorphicTrailingCoeffAt G 0 ^ m
  have ha0 : a ≠ 0 := div_ne_zero
    (hfmer.meromorphicTrailingCoeffAt_ne_zero (hForder ▸ WithTop.coe_ne_top))
    (pow_ne_zero m hGtc0)
  refine ⟨a, (poleOrder_lt_iff hm).2 ?_⟩
  rw [meromorphicOrderAt_congr (cuspFunction_comp₂_eventuallyEq 1 (fun x y ↦ x - a * y ^ m) f g)]
  refine meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq hfmer
    ((MeromorphicAt.const a 0).mul (hgmer.pow m)) hForder ?_ ?_
  · change meromorphicOrderAt ((fun _ : ℂ ↦ a) * G ^ m) 0 = _
    rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const ha0,
      meromorphicOrderAt_pow hgmer, hGorder]
    norm_cast
    exact mul_neg_one (m : ℤ)
  · change _ = meromorphicTrailingCoeffAt ((fun _ : ℂ ↦ a) * G ^ m) 0
    rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_mul (hgmer.pow m),
      meromorphicTrailingCoeffAt_const, hgmer.meromorphicTrailingCoeffAt_pow]
    exact (div_mul_cancel₀ _ (pow_ne_zero m hGtc0)).symm

/-- Cox Lemma 11.10(ii): a level-one modular function holomorphic on `ℍ` is a polynomial
in `j`. -/
theorem CuspData.polynomialInJ_of_holomorphic {f : ℍ → ℂ}
    (hf : LevelOneCuspData f) (hfH : MDiff f) :
    ∃ P : Polynomial ℂ, f = Cox.polynomialIn P j := by
  induction hm : poleOrder 1 f using Nat.strong_induction_on generalizing f with
  | _ m ih =>
  obtain rfl | hm0 := eq_or_ne m 0
  · obtain ⟨c, rfl⟩ := levelOne_constant_of_holomorphic hf hfH
      ((analyticAt_cuspFunction_iff_poleOrder_eq_zero hf.meromorphicAt_cuspFunction_one).2 hm)
    exact ⟨Polynomial.C c, funext fun _ ↦ by simp⟩
  obtain ⟨a, ha⟩ := exists_const_poleOrder_sub_mul_pow_lt hf.meromorphicAt_cuspFunction_one
    j_cuspFunction_meromorphicAt j_poleOrder (hm ▸ Nat.pos_of_ne_zero hm0)
  rw [hm] at ha
  obtain ⟨P, hP⟩ := ih _ ha (cuspData_sub_const_mul_pow 1 hf j_levelOneCuspData a m)
    (hfH.sub ((j_mdifferentiable.pow m).const_smul a)) rfl
  refine ⟨P + Polynomial.monomial m a, funext fun τ ↦ ?_⟩
  have hPτ := congrFun hP τ
  simp only [polynomialIn_apply, Polynomial.eval_add, Polynomial.eval_monomial] at hPτ ⊢
  linear_combination hPτ

private lemma eventually_mdifferentiableAt_atImInfty
    {f : ℍ → ℂ} (hf : LevelOneCuspData f) :
    ∀ᶠ τ in atImInfty, MDiffAt f τ := by
  have hana : ∀ᶠ q in nhdsWithin (0 : ℂ) ({0}ᶜ), AnalyticAt ℂ (cuspFunction 1 f) q :=
    hf.meromorphicAt_cuspFunction_one.eventually_analyticAt
  have hq : Tendsto (fun τ : ℍ ↦ Periodic.qParam 1 (τ : ℂ)) atImInfty
      (nhdsWithin (0 : ℂ) ({0}ᶜ)) :=
    (Periodic.qParam_tendsto one_pos).comp tendsto_coe_atImInfty
  filter_upwards [hq.eventually hana] with τ hτ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hcomp : DifferentiableAt ℂ
      ((cuspFunction 1 f) ∘ Periodic.qParam 1) (τ : ℂ) :=
    hτ.differentiableAt.comp (τ : ℂ) Periodic.differentiable_qParam.differentiableAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  change f (UpperHalfPlane.ofComplex z) = cuspFunction 1 f (Periodic.qParam 1 z)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact (UpperHalfPlane.eq_cuspFunction ⟨z, hz⟩ one_ne_zero hf.periodic).symm

private lemma finite_not_mdifferentiableAt_truncatedFundamentalDomain
    {f : ℍ → ℂ} (hf : LevelOneCuspData f) (y : ℝ) :
    {τ | τ ∈ ModularGroup.truncatedFundamentalDomain y ∧ ¬MDiffAt f τ}.Finite := by
  let K := ModularGroup.truncatedFundamentalDomain y
  let A : Set ℂ := {z | AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) z}
  have hA : A ∈ codiscreteWithin UpperHalfPlane.upperHalfPlaneSet :=
    hf.meromorphicOn.eventually_codiscreteWithin_analyticAt (f ∘ UpperHalfPlane.ofComplex)
  have hKsub : UpperHalfPlane.coe '' K ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    rintro _ ⟨τ, _, rfl⟩
    exact τ.im_pos
  have hAK : A ∈ codiscreteWithin (UpperHalfPlane.coe '' K) :=
    (Filter.codiscreteWithin_mono hKsub) hA
  have hKcompact : IsCompact (UpperHalfPlane.coe '' K) :=
    UpperHalfPlane.isEmbedding_coe.isCompact_iff.mp
      (ModularGroup.isCompact_truncatedFundamentalDomain y)
  have hsingular : ((UpperHalfPlane.coe '' K) \ A).Finite :=
    hKcompact.finite_diff_of_mem_codiscreteWithin hAK
  apply Set.Finite.of_finite_image
    (hsingular.subset ?_) UpperHalfPlane.isEmbedding_coe.injective.injOn
  rintro _ ⟨τ, ⟨hτK, hτ⟩, rfl⟩
  refine ⟨⟨τ, hτK, rfl⟩, ?_⟩
  intro hτan
  exact hτ (UpperHalfPlane.mdifferentiableAt_iff.mpr hτan.differentiableAt)

private lemma exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F J : 𝕜 → 𝕜} {x : 𝕜} (hF : MeromorphicAt F x)
    (hJ : AnalyticAt 𝕜 J x) (hJ0 : J x = 0) :
    ∃ n : ℕ, AnalyticAt 𝕜 (fun z ↦ J z ^ (n + 1) * F z) x := by
  obtain ⟨n, hA⟩ := hF
  obtain ⟨p, hp⟩ := hJ
  have hJan : AnalyticAt 𝕜 J x := ⟨p, hp⟩
  have hD : AnalyticAt 𝕜 (dslope J x) x :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hA' : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n * F z) x := by
    simpa only [smul_eq_mul] using hA
  refine ⟨n, ?_⟩
  have hR : AnalyticAt 𝕜
      (fun z ↦ J z * dslope J x z ^ n * ((z - x) ^ n * F z)) x :=
    (hJan.mul (hD.pow n)).mul hA'
  have heq : (fun z ↦ J z ^ (n + 1) * F z) =
      fun z ↦ J z * dslope J x z ^ n * ((z - x) ^ n * F z) := by
    funext z
    have hz := sub_smul_dslope_of_zero hJ0 z
    simp only [smul_eq_mul] at hz
    rw [pow_succ', ← hz, mul_pow]
    ring
  rw [heq]
  exact hR

private lemma exists_mdifferentiableAt_j_sub_pow_succ_mul
    {f : ℍ → ℂ} (hf : LevelOneCuspData f) (τ : ℍ) :
    ∃ n : ℕ, MDiffAt (fun z ↦ (j z - j τ) ^ (n + 1) * f z) τ := by
  let F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  let J : ℂ → ℂ := fun z ↦ j (UpperHalfPlane.ofComplex z) - j τ
  have hF : MeromorphicAt F (τ : ℂ) := hf.meromorphicAt τ τ.im_pos
  have hjdiff : DifferentiableOn ℂ (j ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable
  have hJ : AnalyticAt ℂ J (τ : ℂ) := by
    exact (hjdiff.analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)).sub analyticAt_const
  have hJ0 : J (τ : ℂ) = 0 := by
    simp [J]
  obtain ⟨n, hn⟩ :=
    exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero hF hJ hJ0
  refine ⟨n, UpperHalfPlane.mdifferentiableAt_iff.mpr ?_⟩
  simpa only [F, J, Function.comp_def] using hn.differentiableAt

private lemma mdifferentiable_polynomialIn_j (P : Polynomial ℂ) :
    MDiff (Cox.polynomialIn P j) := by
  exact UpperHalfPlane.mdifferentiable_iff.mpr <|
    P.differentiable.comp_differentiableOn
      (UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable)

private lemma exists_polynomial_clearing_poles_on_fd_aux {f : ℍ → ℂ}
    (hf : LevelOneCuspData f) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ τ ∈ ModularGroup.fd,
      MDiffAt (fun z ↦ P.eval (j z) * f z) τ := by
  classical
  obtain ⟨y, hy⟩ := (UpperHalfPlane.atImInfty_mem {τ | MDiffAt f τ}).1
    (eventually_mdifferentiableAt_atImInfty hf)
  choose e he using exists_mdifferentiableAt_j_sub_pow_succ_mul hf
  let S := (finite_not_mdifferentiableAt_truncatedFundamentalDomain hf y).toFinset
  let factor (τ : ℍ) : Polynomial ℂ := (Polynomial.X - Polynomial.C (j τ)) ^ (e τ + 1)
  refine ⟨∏ τ ∈ S, factor τ,
    Finset.prod_ne_zero_iff.2 fun τ _ ↦ pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _),
    fun τ hτ ↦ ?_⟩
  by_cases hτf : MDiffAt f τ
  · exact (mdifferentiable_polynomialIn_j _ τ).mul hτf
  have hτS : τ ∈ S := by
    simpa [S, ModularGroup.truncatedFundamentalDomain, hτf, hτ] using
      fun h ↦ hτf (hy τ (le_of_lt h))
  obtain ⟨Q, hQ⟩ := Finset.dvd_prod_of_mem factor hτS
  convert (mdifferentiable_polynomialIn_j Q τ).mul (he τ) using 2 with z
  simp only [hQ, factor, Pi.mul_apply, polynomialIn_apply, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- A function invariant under `SL₂(ℤ)` that is holomorphic at every point of the standard
fundamental domain is holomorphic on the upper half-plane. -/
theorem mdifferentiable_of_forall_mem_fd {H : ℍ → ℂ}
    (hH : ∀ (γ : SL(2, ℤ)) (τ : ℍ), H (γ • τ) = H τ)
    (hfd : ∀ τ ∈ ModularGroup.fd, MDiffAt H τ) : MDiff H := fun τ ↦ by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  simpa only [Function.comp_def, hH] using (hfd _ hγ).comp τ (sl2_mdifferentiable γ τ)

/-- A nonzero polynomial in `j` clears the poles of raw level-one analytic data. -/
theorem CuspData.exists_polynomial_clearing_poles {f : ℍ → ℂ}
    (hf : LevelOneCuspData f) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ MDiff (fun τ ↦ P.eval (j τ) * f τ) := by
  obtain ⟨P, hP0, hPfd⟩ := exists_polynomial_clearing_poles_on_fd_aux hf
  exact ⟨P, hP0, mdifferentiable_of_forall_mem_fd
    (fun γ τ ↦ by simp only [j_modularGroup_smul, hf.apply_sl2_smul]) hPfd⟩

/-- Pole-clearing and polynomiality give rationality for raw level-one analytic data. -/
theorem CuspData.rationalInJ {f : ℍ → ℂ} (hf : LevelOneCuspData f) :
    RationalIn f j := by
  obtain ⟨P, hP, hPdiff⟩ := hf.exists_polynomial_clearing_poles
  obtain ⟨Q, hQ⟩ :=
    ((j_levelOneCuspData.polynomialIn P).mul hf).polynomialInJ_of_holomorphic hPdiff
  refine ⟨Q, P, hP, fun τ hPτ ↦ ?_⟩
  rw [eq_div_iff hPτ, mul_comm]
  simpa using congrFun hQ τ

/-- Cox Theorem 11.9(i): every bundled level-one modular function is rational in `j`. -/
theorem theorem_11_9_i (f : ModularFunction 𝒮ℒ) : RationalIn f j :=
  (CuspData.of_levelOneModularFunction f).rationalInJ

/-- A bundled level-one modular function holomorphic on `ℍ` is a polynomial in `j`. -/
theorem levelOne_polynomialInJ_of_holomorphic (f : ModularFunction 𝒮ℒ) (hf : MDiff f) :
    ∃ P : Polynomial ℂ, (f : ℍ → ℂ) = Cox.polynomialIn P j :=
  (CuspData.of_levelOneModularFunction f).polynomialInJ_of_holomorphic hf

end Cox
