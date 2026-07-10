import Mathlib
import XYin.PhD.Test.JLevelN.Lemma1111
import XYin.PhD.Test.JLevelN.Lemma1110

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

/-!
# Existence of Cox modular equations

This file proves the general Cox modular-equation existence and root relation over `ℂ`
for arbitrary positive level `N`.  It combines the right-coset product from Cox
Lemma 11.11 with the polynomial-in-`j` result formalising Cox Lemma 11.10(ii):
the coefficients of the function-valued Cox product are level-one modular functions,
hence polynomials in `j` once their meromorphicity at the cusp is established.
-/

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

namespace Test

open UpperHalfPlane

noncomputable section

section modularEquation

/-! ## Finite q-order at infinity

This section formalises the finite-growth estimates corresponding to Cox equations
(11.12) and (11.13), using upper-affine representatives.
-/

section FiniteQOrder

/-- A plain weight-zero `SL₂(ℤ)`-invariant function is periodic with period `1`
after precomposition with `UpperHalfPlane.ofComplex`. -/
theorem periodic_comp_of_slashInvariant_one {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  let F : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 0 := {
    toFun := f
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, rfl⟩ := hγ
      exact hslash γ'
  }
  have hper : Periodic (F ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex F (by simp)
  simpa [F] using hper

/-- The level-one q-parameter is manifold-differentiable on the upper half-plane. -/
private theorem qParam_one_MDifferentiable :
    MDiff (fun τ : ℍ => 𝕢 (1 : ℝ) τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hpos : {w : ℂ | 0 < Complex.im w} ∈ nhds z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hqevent :
      (fun w : ℂ => 𝕢 (1 : ℝ) (UpperHalfPlane.ofComplex w))
        =ᶠ[nhds z] Function.Periodic.qParam 1 := by
    filter_upwards [hpos] with w hw
    simp [Function.Periodic.qParam, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact ((Function.Periodic.differentiable_qParam (h := (1 : ℝ)) z).congr_of_eventuallyEq
    hqevent).differentiableWithinAt

/-- The level-one q-parameter, extended by `ofComplex`, has period `1`. -/
private theorem qParam_one_comp_ofComplex_periodic :
    Periodic ((fun τ : ℍ => 𝕢 (1 : ℝ) τ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  intro z
  by_cases hz : 0 < Complex.im z
  · have hz' : 0 < Complex.im (z + (1 : ℝ)) := by
      simpa [Complex.add_im] using hz
    change 𝕢 (1 : ℝ) (UpperHalfPlane.ofComplex (z + (1 : ℝ))) =
      𝕢 (1 : ℝ) (UpperHalfPlane.ofComplex z)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz',
      UpperHalfPlane.ofComplex_apply_of_im_pos hz, Periodic.qParam, Periodic.qParam]
    calc
      Complex.exp (2 * π * Complex.I * (z + (1 : ℝ)) / (1 : ℝ))
          = Complex.exp (2 * π * Complex.I * z / (1 : ℝ) + 2 * π * Complex.I) := by
            congr 1
            ring_nf
            rw [add_comm]
            ring_nf
            norm_num
      _ = Complex.exp (2 * π * Complex.I * z / (1 : ℝ)) *
          Complex.exp (2 * π * Complex.I) := by
        rw [Complex.exp_add]
      _ = Complex.exp (2 * π * Complex.I * z / (1 : ℝ)) := by
        rw [Complex.exp_two_pi_mul_I, mul_one]
  · have hz' : ¬ 0 < Complex.im (z + (1 : ℝ)) := by
      simpa [Complex.add_im] using hz
    exact congrArg (fun τ : ℍ => 𝕢 (1 : ℝ) τ) <|
      UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (not_lt.mp hz') (not_lt.mp hz)

/-- Multiplying a period-one function by a power of the level-one q-parameter
preserves period `1`. -/
private theorem qParam_pow_mul_periodic_one {f : ℍ → ℂ} (M : ℕ)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ)) :
    Periodic
      ((fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ) ∘ UpperHalfPlane.ofComplex) 1 := by
  have hqpow : Periodic
      (fun z : ℂ => (𝕢 (1 : ℝ) (UpperHalfPlane.ofComplex z)) ^ M) (1 : ℝ) := by
    simpa [Function.comp] using
      qParam_one_comp_ofComplex_periodic.comp (fun q : ℂ => q ^ M)
  simpa [Function.comp] using hqpow.mul hfper

/-- A function has finite q-order at infinity if multiplying by a power of
the level-one q-parameter makes it bounded as `im τ → ∞`. -/
def HasFiniteQOrderAtInfty (f : ℍ → ℂ) : Prop :=
  ∃ M : ℕ, IsBoundedAtImInfty (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ)

/-- A fixed power of the level-one q-parameter is bounded at imaginary infinity. -/
private theorem qParam_one_pow_IsBoundedAtImInfty (M : ℕ) :
    IsBoundedAtImInfty (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M) :=
  ((UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) (by norm_num)).pow M).isBigO_one ℝ

/-- Imaginary part computation for the upper-affine map before packaging it in `ℍ`. -/
private lemma upperAffine_im_aux (a d : ℕ+) (b : ℤ) (τ : ℍ) :
    Complex.im (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ)) =
      ((a : ℝ) / (d : ℝ)) * τ.im := by
  rw [← UpperHalfPlane.coe_im τ]
  change Complex.im (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((d : ℝ) : ℂ)) =
    ((a : ℝ) / (d : ℝ)) * (τ : ℂ).im
  rw [Complex.div_ofReal_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.intCast_im, zero_mul, add_zero]
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast PNat.ne_zero d]

/-- The upper-affine representative `(a * τ + b) / d` used in Cox equations
(11.12) and (11.13). -/
noncomputable def upperAffineUpper (a d : ℕ+) (b : ℤ) (τ : ℍ) : ℍ :=
  ⟨((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ), by
    rw [upperAffine_im_aux a d b τ]
    positivity⟩

/-- Imaginary part formula for the upper-affine representative. -/
private theorem upperAffineUpper_im (a d : ℕ+) (b : ℤ) (τ : ℍ) :
    (upperAffineUpper a d b τ).im = ((a : ℝ) / (d : ℝ)) * τ.im :=
  upperAffine_im_aux a d b τ

/-- Upper-affine representatives with positive slope tend to imaginary infinity. -/
private theorem upperAffineUpper_tendsto_atImInfty (a d : ℕ+) (b : ℤ) :
    Tendsto (upperAffineUpper a d b) atImInfty atImInfty := by
  rw [show atImInfty = Filter.comap UpperHalfPlane.im Filter.atTop from rfl,
    Filter.tendsto_comap_iff]
  rw [show UpperHalfPlane.im ∘ upperAffineUpper a d b =
      (fun y : ℝ => ((a : ℝ) / (d : ℝ)) * y) ∘ UpperHalfPlane.im from by
    ext τ
    simp [Function.comp, upperAffineUpper_im]]
  have hscale : 0 < ((a : ℝ) / (d : ℝ)) := by positivity
  exact (Filter.Tendsto.const_mul_atTop hscale Filter.tendsto_id).comp
    Filter.tendsto_comap

/-- The q-ratio in an upper-affine change of variable has norm at most `1`. -/
private lemma upperAffine_qratio_norm_le_one (a d : ℕ+) (y : ℝ) (hy : 0 < y) :
    Real.exp (-2 * Real.pi * y / 1) ^ (a : ℕ) *
        (Real.exp (-2 * Real.pi * (((a : ℝ) / (d : ℝ)) * y) / 1))⁻¹ ≤ 1 := by
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_neg]
  rw [← Real.exp_add]
  rw [Real.exp_le_one_iff]
  have hfrac : (a : ℝ) / d ≤ a := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast d.pos
    calc
      (a : ℝ) / d ≤ (a : ℝ) / 1 := by gcongr
      _ = a := by ring
  have hmul : (a : ℝ) / d * y ≤ (a : ℝ) * y := by gcongr
  nlinarith [Real.pi_pos]

/-- The q-ratio used to rewrite `j` as `qj / q` is bounded at infinity. -/
private theorem upperAffine_qratio_IsBoundedAtImInfty (a d : ℕ+) (b : ℤ) :
    IsBoundedAtImInfty
      (fun τ : ℍ =>
        (𝕢 (1 : ℝ) τ) ^ (a : ℕ) * (𝕢 (1 : ℝ) (upperAffineUpper a d b τ))⁻¹) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨1, 0, fun τ _ => ?_⟩
  rw [norm_mul, norm_pow, norm_inv]
  rw [Function.Periodic.norm_qParam, Function.Periodic.norm_qParam]
  rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, upperAffineUpper_im]
  exact upperAffine_qratio_norm_le_one a d τ.im τ.im_pos

/-- Finite q-order for the upper-affine roots appearing in Cox equations
(11.12) and (11.13). -/
theorem upperAffine_j_finiteQOrder (a d : ℕ+) (b : ℤ) :
    ∃ M : ℕ,
      IsBoundedAtImInfty
        (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * j (upperAffineUpper a d b τ)) := by
  refine ⟨a, ?_⟩
  have hratio := upperAffine_qratio_IsBoundedAtImInfty a d b
  have hqj : IsBoundedAtImInfty (fun τ : ℍ => qj (upperAffineUpper a d b τ)) :=
    qj_IsBoundedAtImInfty.comp_tendsto (upperAffineUpper_tendsto_atImInfty a d b)
  convert hratio.mul hqj using 1
  ext τ
  let w := upperAffineUpper a d b τ
  have hq : 𝕢 (1 : ℝ) (w : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
  change (𝕢 (1 : ℝ) (τ : ℂ)) ^ (a : ℕ) * j w =
    ((𝕢 (1 : ℝ) (τ : ℂ)) ^ (a : ℕ) * (𝕢 (1 : ℝ) (w : ℂ))⁻¹) * qj w
  rw [show qj w = 𝕢 (1 : ℝ) (w : ℂ) * j w by
    simp [qj, Periodic.qParam, Pi.mul_apply]]
  rw [mul_assoc]
  rw [← mul_assoc ((𝕢 (1 : ℝ) (w : ℂ))⁻¹)]
  rw [inv_mul_cancel₀ hq, one_mul]

/-- The gcd used to triangularise `N • γ` is positive. -/
private lemma gcd_pos_of_det (N : ℕ+) (γ : SL(2, ℤ)) :
    0 < Int.gcd ((N : ℤ) * γ 0 0) (γ 1 0) := by
  rw [Nat.pos_iff_ne_zero]
  intro hg0
  have hzero := Int.gcd_eq_zero_iff.mp hg0
  have hNA : (N : ℤ) * γ 0 0 = 0 := hzero.1
  have hC : γ 1 0 = 0 := hzero.2
  have hNnz : (N : ℤ) ≠ 0 := by exact_mod_cast PNat.ne_zero N
  have hA : γ 0 0 = 0 := by
    exact (mul_eq_zero.mp hNA).resolve_left hNnz
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.prop
    rwa [Matrix.det_fin_two] at this
  rw [hA, hC] at hdet
  norm_num at hdet

/-- The triangularisation gcd divides `N`, using the determinant-one relation. -/
private lemma gcd_dvd_N_of_det (N : ℕ+) (γ : SL(2, ℤ)) :
    (Int.gcd ((N : ℤ) * γ 0 0) (γ 1 0) : ℤ) ∣ (N : ℤ) := by
  let g : ℤ := Int.gcd ((N : ℤ) * γ 0 0) (γ 1 0)
  have hg_m : g ∣ (N : ℤ) * γ 0 0 := Int.gcd_dvd_left _ _
  have hg_C : g ∣ γ 1 0 := Int.gcd_dvd_right _ _
  have h1 : g ∣ ((N : ℤ) * γ 0 0) * γ 1 1 := dvd_mul_of_dvd_left hg_m _
  have h2 : g ∣ ((N : ℤ) * γ 0 1) * γ 1 0 := dvd_mul_of_dvd_right hg_C _
  have hsub : g ∣ ((N : ℤ) * γ 0 0) * γ 1 1 - ((N : ℤ) * γ 0 1) * γ 1 0 :=
    dvd_sub h1 h2
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.prop
    rwa [Matrix.det_fin_two] at this
  convert hsub using 1
  calc
    (N : ℤ) = (N : ℤ) * (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) := by
      rw [hdet, mul_one]
    _ = (N : ℤ) * γ 0 0 * γ 1 1 - (N : ℤ) * γ 0 1 * γ 1 0 := by
      ring

/-- Integer coefficients which triangularise the determinant-`N` matrix attached to
`N • (γ • τ)`.  The four displayed identities say that after left multiplication
by a suitable `δ ∈ SL₂(ℤ)`, the matrix has lower-left entry `0` and diagonal
entries `a` and `d`. -/
private theorem exists_upperAffine_integer_coefficients (N : ℕ+) (γ : SL(2, ℤ)) :
    ∃ a d : ℕ+, ∃ b p q r s A B C D : ℤ, ∃ δ : SL(2, ℤ),
      A = γ 0 0 ∧ B = γ 0 1 ∧ C = γ 1 0 ∧ D = γ 1 1 ∧
      δ 0 0 = p ∧ δ 0 1 = q ∧ δ 1 0 = r ∧ δ 1 1 = s ∧
      p * ((N : ℤ) * A) + q * C = (a : ℤ) ∧
      p * ((N : ℤ) * B) + q * D = b ∧
      r * ((N : ℤ) * A) + s * C = 0 ∧
      r * ((N : ℤ) * B) + s * D = (d : ℤ) := by
  let A : ℤ := γ 0 0
  let B : ℤ := γ 0 1
  let C : ℤ := γ 1 0
  let D : ℤ := γ 1 1
  let m : ℤ := (N : ℤ) * A
  let gNat : ℕ := Int.gcd m C
  have hgpos : 0 < gNat := by
    change 0 < Int.gcd ((N : ℤ) * γ 0 0) (γ 1 0)
    exact gcd_pos_of_det N γ
  have hg_ne_int : (gNat : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  let r : ℤ := -(C / (gNat : ℤ))
  let s : ℤ := m / (gNat : ℤ)
  have hcop0 : IsCoprime s (C / (gNat : ℤ)) := by
    simpa [s, m, gNat] using
      (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (p := m) (q := C) hg_ne_int)
  have hcop : IsCoprime r s := by
    have hsym : IsCoprime (C / (gNat : ℤ)) s := hcop0.symm
    simpa [r] using (IsCoprime.neg_left_iff (C / (gNat : ℤ)) s).2 hsym
  obtain ⟨δ, hδr, hδs⟩ := IsCoprime.exists_SL2_row hcop 1
  let p : ℤ := δ 0 0
  let q : ℤ := δ 0 1
  have hdetδ : p * s - q * r = 1 := by
    have := δ.prop
    rw [Matrix.det_fin_two] at this
    simpa [p, q, hδr, hδs] using this
  have hg_dvd_N_int : (gNat : ℤ) ∣ (N : ℤ) := by
    simpa [m, A, C, gNat] using gcd_dvd_N_of_det N γ
  have hg_dvd_N_nat : gNat ∣ (N : ℕ) := by exact_mod_cast hg_dvd_N_int
  let a : ℕ+ := ⟨gNat, hgpos⟩
  let d : ℕ+ := ⟨(N : ℕ) / gNat,
    Nat.div_pos (Nat.le_of_dvd N.pos hg_dvd_N_nat) hgpos⟩
  let b : ℤ := p * ((N : ℤ) * B) + q * D
  have hdetγ : A * D - B * C = 1 := by
    have := γ.prop
    rw [Matrix.det_fin_two] at this
    simpa [A, B, C, D] using this
  have hm_dvd : (gNat : ℤ) ∣ m := by simpa [gNat] using Int.gcd_dvd_left m C
  have hC_dvd : (gNat : ℤ) ∣ C := by simpa [gNat] using Int.gcd_dvd_right m C
  have hm_eq : s * (gNat : ℤ) = m := by
    simpa [s] using Int.ediv_mul_cancel hm_dvd
  have hm_eq' : s * (gNat : ℤ) = (N : ℤ) * A := by simpa [m] using hm_eq
  have hC_eq : (-r) * (gNat : ℤ) = C := by
    have htmp : C / (gNat : ℤ) * (gNat : ℤ) = C := Int.ediv_mul_cancel hC_dvd
    simpa [r] using htmp
  have htop_left : p * ((N : ℤ) * A) + q * C = (gNat : ℤ) := by
    calc
      p * ((N : ℤ) * A) + q * C = p * (s * (gNat : ℤ)) +
          q * ((-r) * (gNat : ℤ)) := by rw [← hm_eq', ← hC_eq]
      _ = (p * s - q * r) * (gNat : ℤ) := by ring
      _ = (gNat : ℤ) := by rw [hdetδ, one_mul]
  have hlower_left : r * ((N : ℤ) * A) + s * C = 0 := by
    calc
      r * ((N : ℤ) * A) + s * C = r * (s * (gNat : ℤ)) +
          s * ((-r) * (gNat : ℤ)) := by rw [← hm_eq', ← hC_eq]
      _ = 0 := by ring
  have hlower_right_mul : (r * ((N : ℤ) * B) + s * D) * (gNat : ℤ) = (N : ℤ) := by
    calc
      (r * ((N : ℤ) * B) + s * D) * (gNat : ℤ)
          = (r * (gNat : ℤ)) * ((N : ℤ) * B) + (s * (gNat : ℤ)) * D := by ring
      _ = (-C) * ((N : ℤ) * B) + ((N : ℤ) * A) * D := by
        have hr : r * (gNat : ℤ) = -C := by linarith
        rw [hr, hm_eq']
      _ = (N : ℤ) * (A * D - B * C) := by ring
      _ = (N : ℤ) := by rw [hdetγ, mul_one]
  have hd_mul_nat : ((N : ℕ) / gNat) * gNat = (N : ℕ) :=
    Nat.div_mul_cancel hg_dvd_N_nat
  have hd_mul_int : (d : ℤ) * (gNat : ℤ) = (N : ℤ) := by
    change (((N : ℕ) / gNat : ℕ) : ℤ) * (gNat : ℤ) = (N : ℤ)
    exact_mod_cast hd_mul_nat
  have hlower_right : r * ((N : ℤ) * B) + s * D = (d : ℤ) := by
    apply mul_right_cancel₀ hg_ne_int
    calc
      (r * ((N : ℤ) * B) + s * D) * (gNat : ℤ) = (N : ℤ) :=
        hlower_right_mul
      _ = (d : ℤ) * (gNat : ℤ) := hd_mul_int.symm
  refine ⟨a, d, b, p, q, r, s, A, B, C, D, δ, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hδr, hδs, htop_left, rfl,
    hlower_left, hlower_right⟩

/-- Matrix algebra identifying the triangularised action with `upperAffineUpper`. -/
private lemma upperAffine_matrix_action_eq
    (N a d : ℕ+) (p q r s A B C D b : ℤ) (τ : ℍ)
    (hdenγ : (C : ℂ) * (τ : ℂ) + (D : ℂ) ≠ 0)
    (htop_left :
      (p : ℂ) * ((N : ℂ) * (A : ℂ)) + (q : ℂ) * (C : ℂ) = (a : ℂ))
    (htop_right :
      (p : ℂ) * ((N : ℂ) * (B : ℂ)) + (q : ℂ) * (D : ℂ) = (b : ℂ))
    (hlower_left :
      (r : ℂ) * ((N : ℂ) * (A : ℂ)) + (s : ℂ) * (C : ℂ) = 0)
    (hlower_right :
      (r : ℂ) * ((N : ℂ) * (B : ℂ)) + (s : ℂ) * (D : ℂ) = (d : ℂ)) :
    (((p : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
          ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (q : ℂ)) /
      ((r : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
          ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (s : ℂ))) =
        (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ)) := by
  have hdenγ' : (τ : ℂ) * (C : ℂ) + (D : ℂ) ≠ 0 := by
    simpa [mul_comm] using hdenγ
  have hd_ne : (d : ℂ) ≠ 0 := by exact_mod_cast PNat.ne_zero d
  have hnum :
      (p : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (q : ℂ) =
        ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
    calc
      (p : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (q : ℂ)
          = (((p : ℂ) * ((N : ℂ) * (A : ℂ)) + (q : ℂ) * (C : ℂ)) *
                (τ : ℂ) +
              ((p : ℂ) * ((N : ℂ) * (B : ℂ)) + (q : ℂ) * (D : ℂ))) /
              ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
            field_simp [hdenγ, hdenγ']
            ring_nf
      _ = ((a : ℂ) * (τ : ℂ) + (b : ℂ)) /
          ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
            rw [htop_left, htop_right]
  have hden :
      (r : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (s : ℂ) =
        (d : ℂ) / ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
    calc
      (r : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (s : ℂ)
          = (((r : ℂ) * ((N : ℂ) * (A : ℂ)) + (s : ℂ) * (C : ℂ)) *
                (τ : ℂ) +
              ((r : ℂ) * ((N : ℂ) * (B : ℂ)) + (s : ℂ) * (D : ℂ))) /
              ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
            field_simp [hdenγ, hdenγ']
            ring_nf
      _ = (d : ℂ) / ((C : ℂ) * (τ : ℂ) + (D : ℂ)) := by
            rw [hlower_left, hlower_right]
            ring
  rw [hnum, hden]
  field_simp [hdenγ, hdenγ', hd_ne]

/-- Every `SL₂(ℤ)` translate of a `jN` root is a `j` of an upper-affine point. -/
private theorem exists_upperAffine_for_jN_sl2_smul
    (N : ℕ+) (γ : SL(2, ℤ)) :
    ∃ a d : ℕ+, ∃ b : ℤ,
      (fun τ : ℍ => jN N (γ • τ)) =
        fun τ : ℍ => j (upperAffineUpper a d b τ) := by
  obtain ⟨a, d, b, p, q, r, s, A, B, C, D, δ, hA, hB, hC, hD, hδp,
    hδq, hδr, hδs, htop_left, htop_right, hlower_left, hlower_right⟩ :=
      exists_upperAffine_integer_coefficients N γ
  refine ⟨a, d, b, ?_⟩
  funext τ
  calc
    jN N (γ • τ) = j (N • (γ • τ)) := rfl
    _ = j (δ • (N • (γ • τ))) := (j_invariant δ (N • (γ • τ))).symm
    _ = j (upperAffineUpper a d b τ) := by
      congr 1
      ext
      simp only [natPosSMul_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
        upperAffineUpper, UpperHalfPlane.coe_mk]
      simp only [algebraMap_int_eq, ← hA, ← hB, ← hC, ← hD, hδp, hδq, hδr, hδs]
      change (((p : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (q : ℂ)) /
          ((r : ℂ) * ((N : ℂ) * (((A : ℂ) * (τ : ℂ) + (B : ℂ)) /
            ((C : ℂ) * (τ : ℂ) + (D : ℂ)))) + (s : ℂ))) =
        (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ))
      have hdenγ : (C : ℂ) * (τ : ℂ) + (D : ℂ) ≠ 0 := by
        have h := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
        simpa [denom, Matrix.SpecialLinearGroup.mapGL, ← hA, ← hC, ← hD,
          algebraMap_int_eq]
          using h
      have htop_left_c : (p : ℂ) * ((N : ℂ) * (A : ℂ)) + (q : ℂ) * (C : ℂ) =
          (a : ℂ) := by
        exact_mod_cast htop_left
      have hlower_left_c : (r : ℂ) * ((N : ℂ) * (A : ℂ)) + (s : ℂ) * (C : ℂ) =
          0 := by
        exact_mod_cast hlower_left
      have hlower_right_c : (r : ℂ) * ((N : ℂ) * (B : ℂ)) + (s : ℂ) * (D : ℂ) =
          (d : ℂ) := by
        exact_mod_cast hlower_right
      have htop_right_c : (p : ℂ) * ((N : ℂ) * (B : ℂ)) + (q : ℂ) * (D : ℂ) =
          (b : ℂ) := by
        exact_mod_cast htop_right
      exact upperAffine_matrix_action_eq N a d p q r s A B C D b τ hdenγ
        htop_left_c htop_right_c hlower_left_c hlower_right_c

/-- A fixed `SL₂(ℤ)` translate of `jN N` has finite q-order at infinity. -/
private theorem jN_sl2_smul_finiteQOrderAtInfty
    (N : ℕ+) (γ : SL(2, ℤ)) :
    HasFiniteQOrderAtInfty (fun τ : ℍ => jN N (γ • τ)) := by
  obtain ⟨a, d, b, h⟩ := exists_upperAffine_for_jN_sl2_smul N γ
  obtain ⟨M, hM⟩ := upperAffine_j_finiteQOrder a d b
  refine ⟨M, ?_⟩
  rw [h]
  exact hM

/-- Every root in Cox equation (11.14) has finite q-order at infinity, via
the upper-affine form of equations (11.12) and (11.13). -/
theorem gamma0RightCosetEval_finiteQOrderAtInfty
    (N : ℕ+) (c : Gamma0RightCosets N) :
    ∃ M : ℕ,
      IsBoundedAtImInfty
        (fun τ : ℍ =>
          (𝕢 (1 : ℝ) τ) ^ M * gamma0RightCosetEval N c τ) := by
  refine Quotient.inductionOn c ?_
  intro γ
  simpa [gamma0RightCosetEval] using jN_sl2_smul_finiteQOrderAtInfty N γ

/-- Constant functions have finite q-order at infinity. -/
private theorem hasFiniteQOrderAtInfty_const (c : ℂ) :
    HasFiniteQOrderAtInfty (fun _ : ℍ => c) := by
  refine ⟨0, ?_⟩
  simpa using (const_boundedAtFilter atImInfty c)

/-- The zero function has finite q-order at infinity. -/
private theorem hasFiniteQOrderAtInfty_zero :
    HasFiniteQOrderAtInfty (fun _ : ℍ => 0) :=
  hasFiniteQOrderAtInfty_const 0

/-- Finite q-order at infinity is preserved by negation. -/
private theorem hasFiniteQOrderAtInfty_neg {f : ℍ → ℂ}
    (hf : HasFiniteQOrderAtInfty f) : HasFiniteQOrderAtInfty (-f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, ?_⟩
  simpa [Pi.neg_apply] using hM.neg

/-- Finite q-order at infinity is preserved by addition. -/
private theorem hasFiniteQOrderAtInfty_add {f g : ℍ → ℂ}
    (hf : HasFiniteQOrderAtInfty f) (hg : HasFiniteQOrderAtInfty g) :
    HasFiniteQOrderAtInfty (f + g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨M + L, ?_⟩
  have hMf : IsBoundedAtImInfty
      (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ L * ((𝕢 (1 : ℝ) τ) ^ M * f τ)) :=
    (qParam_one_pow_IsBoundedAtImInfty L).mul hM
  have hLg : IsBoundedAtImInfty
      (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * ((𝕢 (1 : ℝ) τ) ^ L * g τ)) :=
    (qParam_one_pow_IsBoundedAtImInfty M).mul hL
  convert hMf.add hLg using 1
  ext τ
  simp [Pi.add_apply, pow_add]
  ring

/-- Finite q-order at infinity is preserved by multiplication. -/
private theorem hasFiniteQOrderAtInfty_mul {f g : ℍ → ℂ}
    (hf : HasFiniteQOrderAtInfty f) (hg : HasFiniteQOrderAtInfty g) :
    HasFiniteQOrderAtInfty (f * g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨M + L, ?_⟩
  convert hM.mul hL using 1
  ext τ
  simp [Pi.mul_apply, pow_add]
  ring

/-- Finite q-order at infinity is preserved by finite sums. -/
private theorem hasFiniteQOrderAtInfty_finset_sum {ι : Type*}
    {s : Finset ι} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, HasFiniteQOrderAtInfty (f i)) :
    HasFiniteQOrderAtInfty (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasFiniteQOrderAtInfty_zero
  | insert a s ha ih =>
      have ha_fin : HasFiniteQOrderAtInfty (f a) := hf a (Finset.mem_insert_self a s)
      have hs_fin : HasFiniteQOrderAtInfty (∑ i ∈ s, f i) :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using hasFiniteQOrderAtInfty_add ha_fin hs_fin

/-- An analytic cusp function after multiplying by a q-power gives meromorphicity
of the original cusp function. -/
private theorem cuspFunction_meromorphicAt_of_qpow_shift_analytic
    {f : ℍ → ℂ} {M : ℕ}
    (han : AnalyticAt ℂ
      (cuspFunction 1 (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ)) 0) :
    MeromorphicAt (cuspFunction 1 f) 0 := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨-(M : ℤ),
    cuspFunction 1 (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ), han, ?_⟩
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using
      Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hshift :=
    cuspFunction_qpow_mul_eq (h := (1 : ℝ)) (hh := by norm_num) (f := f)
      (n := M) hq0 hqnorm
  calc
    cuspFunction 1 f q = (q ^ M)⁻¹ * (q ^ M * cuspFunction 1 f q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero M hq0), one_mul]
    _ = (q ^ M)⁻¹ *
        cuspFunction 1 (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ) q := by
      rw [← hshift]
    _ =
        (q - 0) ^ (-(M : ℤ)) •
          cuspFunction 1 (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ) q := by
      simp [smul_eq_mul, zpow_neg, zpow_natCast]

/-- Bridge from Cox-style finite q-order estimates to meromorphicity at the
level-one cusp. -/
theorem cuspFunction_meromorphicAt_of_qpow_shift_bounded
    {f : ℍ → ℂ} {M : ℕ}
    (hper : Periodic
      ((fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ) ∘ UpperHalfPlane.ofComplex) 1)
    (hmdiff : MDiff (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ))
    (hbdd : IsBoundedAtImInfty
      (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ)) :
    MeromorphicAt (cuspFunction 1 f) 0 := by
  apply cuspFunction_meromorphicAt_of_qpow_shift_analytic
  exact UpperHalfPlane.analyticAt_cuspFunction_zero (h := 1)
    (f := fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * f τ)
    (by norm_num) hper hmdiff hbdd

end FiniteQOrder

/-! ## Cox coefficient regularity

Here the Cox coefficients from equation (11.14) are shown to satisfy the
regularity hypotheses needed for the Lemma 11.10(ii) polynomial-in-`j` step.
-/

section CoxCoefficients

/-- Each Cox root `gamma0RightCosetEval N c` is manifold-differentiable on `ℍ`. -/
theorem gamma0RightCosetEval_MDifferentiable (N : ℕ+) (c : Gamma0RightCosets N) :
    MDiff (gamma0RightCosetEval N c) := by
  refine Quotient.inductionOn c ?_
  intro γ
  change MDiff (fun z : ℍ => jN N ((γ : SL(2, ℤ)) • z))
  exact (jN_MDifferentiable N).comp (UpperHalfPlane.mdifferentiable_smul (by simp))

/-- Coefficients of a single Cox linear factor are manifold-differentiable. -/
private lemma coxLinearFactor_coeff_MDifferentiable (N : ℕ+) (c : Gamma0RightCosets N)
    (n : ℕ) :
    MDiff ((Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z) :
      Polynomial (ℍ → ℂ)).coeff n) := by
  cases n with
  | zero =>
      simpa using (gamma0RightCosetEval_MDifferentiable N c).neg
  | succ n =>
      cases n with
      | zero =>
          simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
      | succ n =>
          simp only [Polynomial.coeff_X, Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero]
          change MDiff (fun _ : ℍ => (0 : ℂ))
          exact mdifferentiable_const

/-- Coefficients of a single Cox linear factor have finite q-order when its root does. -/
private theorem coxLinearFactor_coeff_finiteQOrder
    (N : ℕ+) (c : Gamma0RightCosets N) (n : ℕ)
    (hc : HasFiniteQOrderAtInfty (gamma0RightCosetEval N c)) :
    HasFiniteQOrderAtInfty
      ((Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z) :
        Polynomial (ℍ → ℂ)).coeff n) := by
  cases n with
  | zero =>
      simpa using hasFiniteQOrderAtInfty_neg hc
  | succ n =>
      cases n with
      | zero =>
          simpa using hasFiniteQOrderAtInfty_const (1 : ℂ)
      | succ n =>
          simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Nat.right_eq_add,
            Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Polynomial.coeff_C_succ,
            sub_self]
          exact hasFiniteQOrderAtInfty_zero

/-- Differentiability of coefficients is preserved by finite products of polynomials. -/
private lemma polynomial_prod_coeff_MDifferentiable {ι : Type*}
    (P : ι → Polynomial (ℍ → ℂ)) :
    ∀ s : Finset ι, (∀ i ∈ s, ∀ n, MDiff ((P i).coeff n)) →
      ∀ n, MDiff ((s.prod P).coeff n) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ n
      simp only [Finset.prod_empty]
      by_cases hn : n = 0
      · subst n
        simpa [Polynomial.coeff_one] using
          (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
      · simpa [Polynomial.coeff_one, hn] using
          (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))
  | insert a s ha ih =>
      intro hP n
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      exact MDifferentiable.sum fun x hx =>
        (hP a (Finset.mem_insert_self a s) x.1).mul
          (ih (fun i hi n => hP i (Finset.mem_insert_of_mem hi) n) x.2)

/-- Finite q-order of coefficients is preserved by finite products of polynomials. -/
private theorem polynomial_prod_coeff_finiteQOrder {ι : Type*}
    (P : ι → Polynomial (ℍ → ℂ)) :
    ∀ s : Finset ι,
      (∀ i ∈ s, ∀ n, HasFiniteQOrderAtInfty ((P i).coeff n)) →
      ∀ n, HasFiniteQOrderAtInfty ((s.prod P).coeff n) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ n
      simp only [Finset.prod_empty]
      by_cases hn : n = 0
      · subst n
        simpa [Polynomial.coeff_one] using hasFiniteQOrderAtInfty_const (1 : ℂ)
      · simpa [Polynomial.coeff_one, hn] using hasFiniteQOrderAtInfty_zero
  | insert a s ha ih =>
      intro hP n
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      exact hasFiniteQOrderAtInfty_finset_sum fun x hx =>
        hasFiniteQOrderAtInfty_mul
          (hP a (Finset.mem_insert_self a s) x.1)
          (ih (fun i hi n => hP i (Finset.mem_insert_of_mem hi) n) x.2)

/-- Coefficients of the function-valued Cox product are manifold-differentiable. -/
theorem coxPhiFunction_coeff_MDifferentiable (N : ℕ+) (n : ℕ) :
    MDiff ((coxPhiFunction N).coeff n) := by
  classical
  rw [coxPhiFunction]
  exact polynomial_prod_coeff_MDifferentiable
    (fun c : Gamma0RightCosets N =>
      Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))
    Finset.univ (fun c _ n => coxLinearFactor_coeff_MDifferentiable N c n) n

/-- Finite q-order of all Cox roots implies finite q-order of every Cox coefficient. -/
private theorem coxPhiFunction_coeff_finiteQOrder_of_roots
    (N : ℕ+) (n : ℕ)
    (hroot : ∀ c : Gamma0RightCosets N,
      HasFiniteQOrderAtInfty (gamma0RightCosetEval N c)) :
    HasFiniteQOrderAtInfty ((coxPhiFunction N).coeff n) := by
  classical
  rw [coxPhiFunction]
  exact polynomial_prod_coeff_finiteQOrder
    (fun c : Gamma0RightCosets N =>
      Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))
    Finset.univ (fun c _ n => coxLinearFactor_coeff_finiteQOrder N c n (hroot c)) n

/-- A q-power boundedness hypothesis makes a Cox coefficient meromorphic at the cusp. -/
theorem coxPhiFunction_coeff_Meromorphic_of_qpow_shift_bounded
    (N : ℕ+) (n : ℕ)
    (hbounded : ∃ M : ℕ,
      IsBoundedAtImInfty
        (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * (coxPhiFunction N).coeff n τ)) :
    MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0 := by
  obtain ⟨M, hM⟩ := hbounded
  refine cuspFunction_meromorphicAt_of_qpow_shift_bounded (M := M) ?_ ?_ hM
  · exact qParam_pow_mul_periodic_one M
      (periodic_comp_of_slashInvariant_one (coxPhiFunction_coeff_slashInvariant N n))
  · exact (qParam_one_MDifferentiable.pow M).mul
      (coxPhiFunction_coeff_MDifferentiable N n)

/-- The coefficients of Cox equation (11.14) satisfy the meromorphic cusp
hypothesis needed for Cox Lemma 11.10(ii). -/
theorem coxPhiFunction_coeff_Meromorphic (N : ℕ+) (n : ℕ) :
    MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0 :=
  coxPhiFunction_coeff_Meromorphic_of_qpow_shift_bounded N n
    (coxPhiFunction_coeff_finiteQOrder_of_roots N n fun c =>
      gamma0RightCosetEval_finiteQOrderAtInfty N c)

/-- If a Cox coefficient has a meromorphic cusp function and its principal part
can be cancelled by some `P(j)`, then that coefficient is a polynomial in `j`. -/
theorem coxPhiFunction_coeff_polynomialInJ_of_meromorphic_principal
    (N : ℕ+) (n : ℕ)
    (hmero : MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0)
    (hprincipal : ∃ P : Polynomial ℂ,
      poleOrder 1 ((coxPhiFunction N).coeff n - polynomialInJ P) = 0) :
    ∃ P : Polynomial ℂ, (coxPhiFunction N).coeff n = polynomialInJ P :=
  levelOne_meromorphic_polynomialInJ_of_principal_part
    (coxPhiFunction_coeff_slashInvariant N n)
    (coxPhiFunction_coeff_MDifferentiable N n)
    hmero hprincipal

/-- A meromorphic Cox coefficient is a polynomial in `j`, by Cox Lemma 11.10(ii). -/
theorem coxPhiFunction_coeff_polynomialInJ_of_meromorphic
    (N : ℕ+) (n : ℕ)
    (hmero : MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0) :
    ∃ P : Polynomial ℂ, (coxPhiFunction N).coeff n = polynomialInJ P :=
  levelOne_meromorphic_polynomialInJ
    (coxPhiFunction_coeff_slashInvariant N n)
    (coxPhiFunction_coeff_MDifferentiable N n)
    hmero

end CoxCoefficients

/-! ## Modular equation existence

This section assembles Cox equation (11.14) into actual bivariate polynomial
relations.  For general `N`, the result is the complex-coefficient existence
and root relation.
-/

section ModularEquationExistence

/-- Polynomials in `j` as a ring homomorphism into functions on `ℍ`. -/
noncomputable def polynomialInJRingHom : Polynomial ℂ →+* (ℍ → ℂ) where
  toFun := polynomialInJ
  map_zero' := by
    ext z
    simp [polynomialInJ]
  map_one' := by
    ext z
    simp [polynomialInJ]
  map_add' P Q := by
    ext z
    simp [polynomialInJ]
  map_mul' P Q := by
    ext z
    simp [polynomialInJ]

/-- Assemble the bivariate polynomial from chosen coefficient polynomials. -/
noncomputable def coxPhiBivariateOfCoeff (N : ℕ+) (P : ℕ → Polynomial ℂ) :
    Polynomial (Polynomial ℂ) :=
  (coxPhiFunction N).sum fun n _ => Polynomial.C (P n) * Polynomial.X ^ n

/-- Mapping the assembled coefficients through `polynomialInJRingHom` recovers `coxPhiFunction`. -/
theorem coxPhiBivariateOfCoeff_map
    (N : ℕ+) (P : ℕ → Polynomial ℂ)
    (hP : ∀ n, (coxPhiFunction N).coeff n = polynomialInJ (P n)) :
    (coxPhiBivariateOfCoeff N P).map polynomialInJRingHom = coxPhiFunction N := by
  rw [coxPhiBivariateOfCoeff, Polynomial.sum_def, Polynomial.map_sum]
  simp_rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  change (∑ x ∈ (coxPhiFunction N).support,
      Polynomial.C (polynomialInJ (P x)) * Polynomial.X ^ x) =
    coxPhiFunction N
  simp_rw [← hP]
  simpa [Polynomial.sum_def] using Polynomial.sum_C_mul_X_pow_eq (coxPhiFunction N)

/-- If every Cox coefficient is a polynomial in `j`, then the modular equation exists. -/
theorem cox_modularEquation_exists_of_coeff_polynomialInJ (N : ℕ+)
    (hcoeff : ∀ n, ∃ P : Polynomial ℂ,
      (coxPhiFunction N).coeff n = polynomialInJ P) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 := by
  let P : ℕ → Polynomial ℂ := fun n => Classical.choose (hcoeff n)
  have hP : ∀ n, (coxPhiFunction N).coeff n = polynomialInJ (P n) :=
    fun n => Classical.choose_spec (hcoeff n)
  refine ⟨coxPhiBivariateOfCoeff N P, coxPhiBivariateOfCoeff_map N P hP, ?_⟩
  rw [coxPhiBivariateOfCoeff_map N P hP]
  exact coxPhiFunction_eval_jN N

/-- Conditional modular-equation assembly assuming meromorphic coefficients and
explicit principal-part cancellations. -/
theorem cox_modularEquation_exists_of_coeff_meromorphic_principal (N : ℕ+)
    (hmero : ∀ n, MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0)
    (hprincipal : ∀ n, ∃ P : Polynomial ℂ,
      poleOrder 1 ((coxPhiFunction N).coeff n - polynomialInJ P) = 0) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 :=
  cox_modularEquation_exists_of_coeff_polynomialInJ N fun n =>
    coxPhiFunction_coeff_polynomialInJ_of_meromorphic_principal N n
      (hmero n) (hprincipal n)

/-- Modular-equation assembly assuming all Cox coefficients are meromorphic at
the level-one cusp. -/
theorem cox_modularEquation_exists_of_coeff_meromorphic (N : ℕ+)
    (hmero : ∀ n, MeromorphicAt (cuspFunction 1 ((coxPhiFunction N).coeff n)) 0) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 :=
  cox_modularEquation_exists_of_coeff_polynomialInJ N fun n =>
    coxPhiFunction_coeff_polynomialInJ_of_meromorphic N n (hmero n)

/-- Modular-equation assembly from finite q-order bounds on all Cox coefficients. -/
theorem cox_modularEquation_exists_of_coeff_qpow_shift_bounded (N : ℕ+)
    (hbounded : ∀ n, ∃ M : ℕ,
      IsBoundedAtImInfty
        (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * (coxPhiFunction N).coeff n τ)) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 :=
  cox_modularEquation_exists_of_coeff_meromorphic N fun n =>
    coxPhiFunction_coeff_Meromorphic_of_qpow_shift_bounded N n (hbounded n)

/-- Modular-equation assembly from finite q-order bounds on the Cox roots. -/
theorem cox_modularEquation_exists_of_roots_qpow_shift_bounded (N : ℕ+)
    (hroot : ∀ c : Gamma0RightCosets N, ∃ M : ℕ,
      IsBoundedAtImInfty
        (fun τ : ℍ => (𝕢 (1 : ℝ) τ) ^ M * gamma0RightCosetEval N c τ)) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 :=
  cox_modularEquation_exists_of_coeff_qpow_shift_bounded N fun n =>
    coxPhiFunction_coeff_finiteQOrder_of_roots N n hroot

/-- Cox equation (11.14) after replacing coefficient functions by polynomials
in `j`, as a polynomial over `Polynomial ℂ`. -/
theorem cox_modularEquation_exists (N : ℕ+) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ.map polynomialInJRingHom = coxPhiFunction N ∧
      Polynomial.eval (jN N) (Φ.map polynomialInJRingHom) = 0 :=
  cox_modularEquation_exists_of_roots_qpow_shift_bounded N fun c =>
    gamma0RightCosetEval_finiteQOrderAtInfty N c

/-- Evaluating a mapped bivariate polynomial as a function agrees with
`evalEval` at `(j z, f z)`. -/
theorem polynomialInJRingHom_eval_apply
    (Φ : Polynomial (Polynomial ℂ)) (f : ℍ → ℂ) (z : ℍ) :
    Polynomial.eval f (Φ.map polynomialInJRingHom) z = Φ.evalEval (j z) (f z) := by
  change evalAtUpper z (Polynomial.eval f (Φ.map polynomialInJRingHom)) =
    Φ.evalEval (j z) (f z)
  rw [← Polynomial.eval₂_at_apply (p := Φ.map polynomialInJRingHom) (evalAtUpper z) f]
  rw [Polynomial.eval₂_map]
  have hcomp : (evalAtUpper z).comp polynomialInJRingHom =
      Polynomial.evalRingHom (j z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [evalAtUpper, polynomialInJRingHom, polynomialInJ]
    · simp [evalAtUpper, polynomialInJRingHom, polynomialInJ]
  change Polynomial.eval₂ ((evalAtUpper z).comp polynomialInJRingHom) (f z) Φ =
    Φ.evalEval (j z) (f z)
  rw [hcomp]
  rw [Polynomial.eval₂_evalRingHom]

/-- Pointwise bivariate form of Cox equation (11.14): `Φ(j z, jN N z) = 0`. -/
theorem cox_modularEquation_exists_bivariate (N : ℕ+) :
    ∃ Φ : Polynomial (Polynomial ℂ),
      Φ ≠ 0 ∧
        Φ.map polynomialInJRingHom = coxPhiFunction N ∧
          ∀ z : ℍ, Φ.evalEval (j z) (jN N z) = 0 := by
  obtain ⟨Φ, hmap, hroot⟩ := cox_modularEquation_exists N
  refine ⟨Φ, ?_, hmap, ?_⟩
  · intro hΦ
    have hzero : coxPhiFunction N = 0 := by
      rw [← hmap, hΦ, Polynomial.map_zero]
    exact (coxPhiFunction_monic N).ne_zero hzero
  · intro z
    have hz := congrFun hroot z
    rw [polynomialInJRingHom_eval_apply] at hz
    simpa using hz

/-- The bivariate-to-multivariate polynomial equivalence preserves evaluation. -/
private theorem bivariate_equivMvPolynomial_eval
    (Φ : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (Polynomial.Bivariate.equivMvPolynomial ℂ Φ) =
      Φ.evalEval x y := by
  rw [← Polynomial.coe_aevalAeval_eq_evalEval x y]
  change MvPolynomial.aeval ![x, y] (Polynomial.Bivariate.equivMvPolynomial ℂ Φ) =
    Polynomial.aevalAeval x y Φ
  change ((MvPolynomial.aeval ![x, y]).comp
      (Polynomial.Bivariate.equivMvPolynomial ℂ).toAlgHom) Φ =
    Polynomial.aevalAeval x y Φ
  congr 1
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [Polynomial.Bivariate.equivMvPolynomial]
  · simp [Polynomial.Bivariate.equivMvPolynomial]

/-- Cox equation (11.14) as a nonzero multivariate polynomial in two
variables. -/
theorem cox_modularEquation_exists_mvPolynomial (N : ℕ+) :
    ∃ Φ : MvPolynomial (Fin 2) ℂ,
      Φ ≠ 0 ∧ ∀ z : ℍ, MvPolynomial.eval ![j z, jN N z] Φ = 0 := by
  obtain ⟨Φ, hΦ, _, hroot⟩ := cox_modularEquation_exists_bivariate N
  let Ψ := Polynomial.Bivariate.equivMvPolynomial ℂ Φ
  refine ⟨Ψ, ?_, ?_⟩
  · intro hΨ
    apply hΦ
    apply (Polynomial.Bivariate.equivMvPolynomial ℂ).injective
    simpa [Ψ] using hΨ
  · intro z
    rw [bivariate_equivMvPolynomial_eval]
    exact hroot z


end ModularEquationExistence

end modularEquation

end

end Test
