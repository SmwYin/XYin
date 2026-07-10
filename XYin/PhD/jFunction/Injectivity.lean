import XYin.PhD.jFunction.jLevelN
import XYin.Workshop.L_L_bar_real

set_option linter.style.header false

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

noncomputable section

namespace PeriodPair

/-- Two period pairs are homothetic if their period lattices agree after scaling one of them by a
nonzero complex number. -/
def Homothetic (L M : PeriodPair) : Prop :=
  ∃ a : ℂˣ, (a • L).lattice = M.lattice

end PeriodPair

namespace UpperHalfPlane

/-- The normalized period pair attached to a point of the upper half-plane, with lattice
`ℤ + ℤτ`. -/
noncomputable def periodPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    refine LinearIndependent.pair_iff.mpr fun a b hab => ?_
    have hb_im : b * τ.im = 0 := by
      simpa [Complex.real_smul] using congrArg Complex.im hab
    have hb : b = 0 := (mul_eq_zero.mp hb_im).resolve_right τ.im_ne_zero
    have ha_re : a = 0 := by
      simpa [Complex.real_smul, hb] using congrArg Complex.re hab
    exact ⟨ha_re, hb⟩

end UpperHalfPlane

section PeriodPairEisenstein

open EisensteinSeries
open scoped CongruenceSubgroup

/-- The lattice Eisenstein sum of `ℤ + ℤτ` is the full Eisenstein series `∑ (mτ + n)⁻ᵏ`,
which mathlib expresses as `ζ(k) · eisensteinSeries`. -/
private lemma periodPair_G_eq (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (UpperHalfPlane.periodPair τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ := by
  rw [← tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ, PeriodPair.G]
  rw [← (((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans
    (UpperHalfPlane.periodPair τ).latticeEquivProd.toEquiv.symm).tsum_eq
    (f := fun l : (UpperHalfPlane.periodPair τ).lattice => ((l : ℂ) ^ k)⁻¹)]
  refine tsum_congr fun v => ?_
  have hcoe : (((UpperHalfPlane.periodPair τ).latticeEquivProd.symm (v 1, v 0) : ℂ)) =
      (v 1 : ℂ) + (v 0 : ℂ) * τ := by
    simpa [UpperHalfPlane.periodPair] using
      (UpperHalfPlane.periodPair τ).latticeEquiv_symm_apply (v 1, v 0)
  simp only [Equiv.trans_apply, finTwoArrowEquiv_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    eisSummand, zpow_neg, zpow_natCast, Equiv.toFun_as_coe, piFinTwoEquiv_apply,
    LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe]
  rw [show ((UpperHalfPlane.periodPair τ).latticeEquivProd.symm (v 1, v 0) : ℂ) =
      (v 1 : ℂ) + (v 0 : ℂ) * τ from hcoe]
  ring_nf

private lemma riemannZeta_six' : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_six, Nat.factorial] at h
  rw [h]
  ring

private lemma E4_apply_eisensteinSeries (τ : ℍ) :
    E4 τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 4 τ := by
  rw [show E4 τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 4 τ from rfl,
    eisensteinSeriesSIF_apply]
  simp

private lemma E6_apply_eisensteinSeries (τ : ℍ) :
    E6 τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 6 τ := by
  rw [show E6 τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 6 τ from rfl,
    eisensteinSeriesSIF_apply]
  simp

/-- `g₂` of the lattice `ℤ + ℤτ` in terms of the normalised Eisenstein series `E₄`. -/
private lemma periodPair_g₂_eq (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E4 τ := by
  have hE := E4_apply_eisensteinSeries τ
  rw [PeriodPair.g₂, periodPair_G_eq τ (by norm_num)]
  norm_num [riemannZeta_four]
  rw [show eisensteinSeries (N := 1) 0 4 τ = 2 * E4 τ by rw [hE]; ring]
  ring

/-- `g₃` of the lattice `ℤ + ℤτ` in terms of the normalised Eisenstein series `E₆`. -/
private lemma periodPair_g₃_eq (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E6 τ := by
  have hE := E6_apply_eisensteinSeries τ
  rw [PeriodPair.g₃, periodPair_G_eq τ (by norm_num)]
  norm_num [riemannZeta_six']
  rw [show eisensteinSeries (N := 1) 0 6 τ = 2 * E6 τ by rw [hE]; ring]
  ring

/-- The modular discriminant as a polynomial in the Eisenstein series, pointwise. -/
private lemma Delta_eq_E4_E6 (z : ℍ) : Delta z = (E4 z ^ 3 - E6 z ^ 2) / 1728 := by
  rw [show Delta z = (ModForm_mk _ _ Delta_E4_E6_aux) z by rw [Delta_E4_eqn]; rfl,
    Delta_E4_E6_eq]
  simp only [pow_two, pow_three, DirectSum.of_mul_of, DirectSum.sub_apply,
    ModularForm.IsGLPos.smul_apply, ModularForm.sub_apply, smul_eq_mul]
  rw [
    show ((((DirectSum.of (ModularForm Γ(1)) (4 + (4 + 4)))
            (GradedMonoid.GMul.mul _root_.E₄
              (GradedMonoid.GMul.mul _root_.E₄ _root_.E₄))) 12) z) = E4 z ^ 3 by
      change (((DirectSum.of (ModularForm Γ(1)) 12)
          (GradedMonoid.GMul.mul _root_.E₄
            (GradedMonoid.GMul.mul _root_.E₄ _root_.E₄))) 12) z = E4 z ^ 3
      rw [DirectSum.of_eq_same]
      change E4 z * (E4 z * E4 z) = E4 z ^ 3
      ring,
    show ((((DirectSum.of (ModularForm Γ(1)) (6 + 6))
            (GradedMonoid.GMul.mul _root_.E₆ _root_.E₆)) 12) z) = E6 z ^ 2 by
      change (((DirectSum.of (ModularForm Γ(1)) 12)
          (GradedMonoid.GMul.mul _root_.E₆ _root_.E₆)) 12) z = E6 z ^ 2
      rw [DirectSum.of_eq_same]
      change E6 z * E6 z = E6 z ^ 2
      ring]
  rw [div_eq_mul_inv]
  ring

private lemma E4_E6_sub_ne_zero (z : ℍ) : E4 z ^ 3 - E6 z ^ 2 ≠ 0 := by
  intro h
  have hΔ : Delta z ≠ 0 := by simpa [Delta_apply] using Δ_ne_zero z
  exact hΔ (by rw [Delta_eq_E4_E6, h, zero_div])

end PeriodPairEisenstein

/-- The analytic modular `j`-function agrees with the period-lattice `j`-invariant for the
normalized lattice `ℤ + ℤτ`. -/
theorem j_eq_periodPair_j (τ : ℍ) : j τ = (UpperHalfPlane.periodPair τ).j := by
  rw [PeriodPair.j, PeriodPair.discriminant, periodPair_g₂_eq, periodPair_g₃_eq, j,
    Delta_eq_E4_E6]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΔ := E4_E6_sub_ne_zero τ
  have hd1 : (E4 τ ^ 3 - E6 τ ^ 2) / 1728 ≠ 0 := div_ne_zero hΔ (by norm_num)
  have hd2 : (4 * (π : ℂ) ^ 4 / 3 * E4 τ) ^ 3 - 27 * (8 * (π : ℂ) ^ 6 / 27 * E6 τ) ^ 2 ≠ 0 := by
    rw [show (4 * (π : ℂ) ^ 4 / 3 * E4 τ) ^ 3 - 27 * (8 * (π : ℂ) ^ 6 / 27 * E6 τ) ^ 2 =
        64 * (π : ℂ) ^ 12 / 27 * (E4 τ ^ 3 - E6 τ ^ 2) by ring]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hπ)) (by norm_num)) hΔ
  rw [div_eq_div_iff hd1 hd2]
  ring

section DiscriminantNeZero

/-- Every period pair is homothetic to a normalized one `ℤ + ℤτ` with `τ ∈ ℍ`. -/
private lemma exists_smul_lattice_eq_periodPair (L : PeriodPair) :
    ∃ (τ : ℍ) (a : ℂˣ), (a • L).lattice = (UpperHalfPlane.periodPair τ).lattice := by
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hω₂ : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  have him : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro h0
    have hτ : (L.ω₂ / L.ω₁ : ℂ) = ((L.ω₂ / L.ω₁).re : ℝ) := by
      exact Complex.ext (by simp) (by simpa using h0)
    have hzero : ((L.ω₂ / L.ω₁).re : ℝ) • L.ω₁ + (-1 : ℝ) • L.ω₂ = 0 := by
      rw [Complex.real_smul, Complex.real_smul, ← hτ]
      push_cast
      field_simp
      ring
    obtain ⟨-, ht⟩ := LinearIndependent.pair_iff.mp L.indep _ _ hzero
    norm_num at ht
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨⟨L.ω₁ / L.ω₂, ?_⟩, Units.mk0 L.ω₂⁻¹ (inv_ne_zero hω₂), ?_⟩
    · rw [show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div L.ω₂ L.ω₁).symm, Complex.inv_im]
      have hns : 0 < Complex.normSq (L.ω₂ / L.ω₁) :=
        Complex.normSq_pos.mpr (div_ne_zero hω₂ hω₁)
      exact div_pos (by linarith) hns
    · rw [PeriodPair.lattice, PeriodPair.lattice]
      congr 1
      rw [PeriodPair.smul_ω₁, PeriodPair.smul_ω₂]
      rw [show ((Units.mk0 L.ω₂⁻¹ (inv_ne_zero hω₂) : ℂˣ) : ℂ) = L.ω₂⁻¹ from rfl]
      rw [Set.pair_comm]
      congr 1
      · exact inv_mul_cancel₀ hω₂
      · exact congrArg _ (inv_mul_eq_div _ _)
  · refine ⟨⟨L.ω₂ / L.ω₁, hpos⟩, Units.mk0 L.ω₁⁻¹ (inv_ne_zero hω₁), ?_⟩
    rw [PeriodPair.lattice, PeriodPair.lattice]
    congr 1
    rw [PeriodPair.smul_ω₁, PeriodPair.smul_ω₂]
    rw [show ((Units.mk0 L.ω₁⁻¹ (inv_ne_zero hω₁) : ℂˣ) : ℂ) = L.ω₁⁻¹ from rfl]
    congr 1
    · exact inv_mul_cancel₀ hω₁
    · exact congrArg _ (inv_mul_eq_div _ _)

private lemma periodPair_discriminant_eq (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).discriminant =
      64 * (π : ℂ) ^ 12 / 27 * (E4 τ ^ 3 - E6 τ ^ 2) := by
  rw [PeriodPair.discriminant, periodPair_g₂_eq, periodPair_g₃_eq]
  ring

/-- **The discriminant of a period lattice never vanishes.** This is obtained by normalizing the
lattice to `ℤ + ℤτ` and using the nonvanishing of the modular discriminant. -/
theorem PeriodPair.discriminant_ne_zero (L : PeriodPair) : L.discriminant ≠ 0 := by
  obtain ⟨τ, a, ha⟩ := exists_smul_lattice_eq_periodPair L
  have hcongr : (a • L).discriminant = (UpperHalfPlane.periodPair τ).discriminant := by
    rw [PeriodPair.discriminant, PeriodPair.discriminant,
      PeriodPair.g₂_congr ha, PeriodPair.g₃_congr ha]
  rw [L.discriminant_smul a] at hcongr
  intro h0
  rw [h0, mul_zero] at hcongr
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : (UpperHalfPlane.periodPair τ).discriminant ≠ 0 := by
    rw [periodPair_discriminant_eq τ]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hπ))
      (by norm_num)) (E4_E6_sub_ne_zero τ)
  exact hne hcongr.symm

end DiscriminantNeZero

namespace PeriodPair

private lemma g₂_eq_zero_of_j_eq_zero {L : PeriodPair} (h : L.j = 0) : L.g₂ = 0 := by
  have hΔ := L.discriminant_ne_zero
  rw [j, div_eq_zero_iff] at h
  rcases h with h | h
  · have h3 : L.g₂ ^ 3 = 0 := by linear_combination h / 1728
    exact pow_eq_zero_iff (by norm_num) |>.mp h3
  · exact absurd h hΔ

private lemma g₃_eq_zero_of_j_eq_1728 {L : PeriodPair} (h : L.j = 1728) : L.g₃ = 0 := by
  have hΔ := L.discriminant_ne_zero
  rw [j, div_eq_iff hΔ, discriminant] at h
  have h2 : L.g₃ ^ 2 = 0 := by linear_combination h / 46656
  exact pow_eq_zero_iff (by norm_num) |>.mp h2

/-- Uniformisation/classification input: the `j`-invariant classifies complex period lattices up
to homothety. -/
theorem homothetic_of_j_eq {L M : PeriodPair} (h : L.j = M.j) : L.Homothetic M := by
  have hΔL := L.discriminant_ne_zero
  have hΔM := M.discriminant_ne_zero
  by_cases hg₂L : L.g₂ = 0
  · have hg₂M : M.g₂ = 0 :=
      g₂_eq_zero_of_j_eq_zero (by rw [← h, L.j_eq_zero_of_g₂_eq_zero hg₂L])
    have hg₃L := L.g₃_ne_zero_of_g₂_eq_zero hΔL hg₂L
    have hg₃M := M.g₃_ne_zero_of_g₂_eq_zero hΔM hg₂M
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₃ / M.g₃) (n := 6) (by norm_num)
    have hc0 : c ≠ 0 := by
      intro h0
      apply hg₃L
      have hd : L.g₃ / M.g₃ = 0 := by rw [← hc, h0]; norm_num
      exact (div_eq_zero_iff.mp hd).resolve_right hg₃M
    refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
    · rw [g₂_smul, hg₂L, hg₂M, mul_zero]
    · rw [g₃_smul]
      rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc]
      field_simp
  · by_cases hg₃L : L.g₃ = 0
    · have hg₃M : M.g₃ = 0 :=
        g₃_eq_zero_of_j_eq_1728 (by rw [← h, L.j_eq_1728_of_g₃_eq_zero hΔL hg₃L])
      have hg₂M := M.g₂_ne_zero_of_g₃_eq_zero hΔM hg₃M
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / M.g₂) (n := 4) (by norm_num)
      have hc0 : c ≠ 0 := by
        intro h0
        apply hg₂L
        have hd : L.g₂ / M.g₂ = 0 := by rw [← hc, h0]; norm_num
        exact (div_eq_zero_iff.mp hd).resolve_right hg₂M
      refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
      · rw [g₂_smul]
        rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc]
        field_simp
      · rw [g₃_smul, hg₃L, hg₃M, mul_zero]
    · have hg₂M : M.g₂ ≠ 0 := fun h0 =>
        hg₂L (g₂_eq_zero_of_j_eq_zero (by rw [h, M.j_eq_zero_of_g₂_eq_zero h0]))
      have hg₃M : M.g₃ ≠ 0 := fun h0 =>
        hg₃L (g₃_eq_zero_of_j_eq_1728 (by rw [h, M.j_eq_1728_of_g₃_eq_zero hΔM h0]))
      have hcross : L.g₂ ^ 3 * M.g₃ ^ 2 = M.g₂ ^ 3 * L.g₃ ^ 2 := by
        rw [j, j, div_eq_div_iff hΔL hΔM, discriminant, discriminant] at h
        linear_combination -h / 46656
      obtain ⟨c, hc⟩ :=
        IsAlgClosed.exists_pow_nat_eq (L.g₃ * M.g₂ / (M.g₃ * L.g₂)) (n := 2) (by norm_num)
      have hb0 : L.g₃ * M.g₂ / (M.g₃ * L.g₂) ≠ 0 :=
        div_ne_zero (mul_ne_zero hg₃L hg₂M) (mul_ne_zero hg₃M hg₂L)
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0] at hc
        exact hb0 (by rw [← hc]; norm_num)
      have hc4 : c ^ 4 = L.g₂ / M.g₂ := by
        rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, div_pow, div_eq_div_iff
          (pow_ne_zero _ (mul_ne_zero hg₃M hg₂L)) hg₂M]
        linear_combination -hcross
      have hc6 : c ^ 6 = L.g₃ / M.g₃ := by
        rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc, div_pow, div_eq_div_iff
          (pow_ne_zero _ (mul_ne_zero hg₃M hg₂L)) hg₃M]
        linear_combination -L.g₃ * M.g₃ * hcross
      refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
      · rw [g₂_smul]
        rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc4]
        field_simp
      · rw [g₃_smul]
        rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc6]
        field_simp

end PeriodPair

section Sl2Homothety

/-- Membership in the normalized lattice `ℤ + ℤτ`, spelled with integer coefficients. -/
private lemma mem_periodPair_lattice {τ : ℍ} {x : ℂ} :
    x ∈ (UpperHalfPlane.periodPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * τ = x := by
  rw [PeriodPair.mem_lattice]
  simp [UpperHalfPlane.periodPair]

/-- Two integer combinations of `1` and `τ` agree only if the coefficients agree. -/
private lemma int_comb_injective {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * τ = (m' : ℂ) + n' * τ) : m = m' ∧ n = n' := by
  have hzero : ((m - m' : ℤ) : ℝ) • (UpperHalfPlane.periodPair τ).ω₁ +
      ((n - n' : ℤ) : ℝ) • (UpperHalfPlane.periodPair τ).ω₂ = 0 := by
    change ((m - m' : ℤ) : ℝ) • (1 : ℂ) + ((n - n' : ℤ) : ℝ) • (τ : ℂ) = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ :=
    LinearIndependent.pair_iff.mp (UpperHalfPlane.periodPair τ).indep _ _ hzero
  constructor
  · have : ((m - m' : ℤ) : ℝ) = 0 := h1
    have := sub_eq_zero.mp (by exact_mod_cast this)
    exact this
  · have : ((n - n' : ℤ) : ℝ) = 0 := h2
    have := sub_eq_zero.mp (by exact_mod_cast this)
    exact this

/-- Homothety of normalized upper-half-plane lattices is equivalent to equality modulo the usual
`SL(2, ℤ)` action. -/
theorem periodPair_homothetic_iff_exists_sl2_smul_eq {z w : ℍ} :
    PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w) ↔
      ∃ γ : SL(2, ℤ), γ • z = w := by
  constructor
  · rintro ⟨α, hα⟩
    -- Read off integer matrices in both directions from the lattice equality.
    have hz1 : (α : ℂ) * z ∈ (UpperHalfPlane.periodPair w).lattice := by
      rw [← hα]
      exact (UpperHalfPlane.periodPair z).mem_smul_lattice.mpr
        ⟨z, mem_periodPair_lattice.mpr ⟨0, 1, by simp⟩, rfl⟩
    have hz2 : (α : ℂ) ∈ (UpperHalfPlane.periodPair w).lattice := by
      rw [← hα]
      exact (UpperHalfPlane.periodPair z).mem_smul_lattice.mpr
        ⟨1, mem_periodPair_lattice.mpr ⟨1, 0, by simp⟩, by simp⟩
    obtain ⟨b, a, hab⟩ := mem_periodPair_lattice.mp hz1
    obtain ⟨d, c, hcd⟩ := mem_periodPair_lattice.mp hz2
    have hw1 : ((1 : ℂ)) ∈ ((α : ℂˣ) • UpperHalfPlane.periodPair z).lattice := by
      rw [hα]; exact mem_periodPair_lattice.mpr ⟨1, 0, by simp⟩
    have hw2 : ((w : ℂ)) ∈ ((α : ℂˣ) • UpperHalfPlane.periodPair z).lattice := by
      rw [hα]; exact mem_periodPair_lattice.mpr ⟨0, 1, by simp⟩
    obtain ⟨y1, hy1, hy1e⟩ := (UpperHalfPlane.periodPair z).mem_smul_lattice.mp hw1
    obtain ⟨y2, hy2, hy2e⟩ := (UpperHalfPlane.periodPair z).mem_smul_lattice.mp hw2
    obtain ⟨p, q, hpq⟩ := mem_periodPair_lattice.mp hy1
    obtain ⟨r, s, hrs⟩ := mem_periodPair_lattice.mp hy2
    -- Coefficient equations from linear independence of (1, w).
    have he1 : (1 : ℂ) = (q : ℂ) * b + p * d + ((q : ℂ) * a + p * c) * w := by
      linear_combination hy1e - (α : ℂ) * hpq - (p : ℂ) * hcd - (q : ℂ) * hab
    obtain ⟨h2, h1⟩ := int_comb_injective (show ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * w =
      ((q * b + p * d : ℤ) : ℂ) + ((q * a + p * c : ℤ) : ℂ) * w by
        push_cast; linear_combination he1)
    have he2 : (w : ℂ) = (s : ℂ) * b + r * d + ((s : ℂ) * a + r * c) * w := by
      linear_combination hy2e - (α : ℂ) * hrs - (r : ℂ) * hcd - (s : ℂ) * hab
    obtain ⟨h4, h3⟩ := int_comb_injective (show ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * w =
      ((s * b + r * d : ℤ) : ℂ) + ((s * a + r * c : ℤ) : ℂ) * w by
        push_cast; linear_combination he2)
    -- The change-of-basis matrix has determinant ±1.
    have hdet : (a * d - b * c) * (p * s - q * r) = 1 := by
      linear_combination (-(s * b) - r * d) * h1.symm + (s * a + r * c) * h2.symm + h3.symm
    have hαd : (α : ℂ) = (d : ℂ) + c * w := hcd.symm
    have hzval : (z : ℂ) = ((b : ℂ) + a * w) / ((d : ℂ) + c * w) := by
      rw [← hαd, hab, mul_div_cancel_left₀ _ α.ne_zero]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨hD, -⟩ | ⟨hD, -⟩
    · -- determinant 1: the matrix acts on `w` and sends it to `z`.
      have hdet1 : Matrix.det !![a, b; c, d] = 1 := by
        rw [Matrix.det_fin_two_of]; omega
      set γ' : SL(2, ℤ) := ⟨!![a, b; c, d], hdet1⟩ with hγ'
      refine ⟨γ'⁻¹, ?_⟩
      have hcoe : ((γ' • w : ℍ) : ℂ) = (z : ℂ) := by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply, hzval, hγ']
        simp [algebraMap_int_eq]
        ring
      have hsmul : γ' • w = z := UpperHalfPlane.ext hcoe
      rw [← hsmul, inv_smul_smul]
    · -- determinant -1 is impossible: it would send `w` to `-z ∉ ℍ`.
      exfalso
      have hdet1 : Matrix.det !![-a, -b; c, d] = 1 := by
        rw [Matrix.det_fin_two_of]
        have : a * d - b * c = -1 := hD
        ring_nf
        omega
      set γ'' : SL(2, ℤ) := ⟨!![-a, -b; c, d], hdet1⟩ with hγ''
      have hcoe : ((γ'' • w : ℍ) : ℂ) = -(z : ℂ) := by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply, hzval, hγ'']
        simp [algebraMap_int_eq]
        ring
      have him := (γ'' • w).im_pos
      rw [UpperHalfPlane.im, hcoe, Complex.neg_im, UpperHalfPlane.coe_im] at him
      linarith [z.im_pos]
  · rintro ⟨γ, rfl⟩
    -- Scaling by `denom γ z = c z + d` carries `ℤ + ℤz` onto `ℤ + ℤ(γ • z)`.
    set a : ℤ := γ 0 0 with ha
    set b : ℤ := γ 0 1 with hb
    set c : ℤ := γ 1 0 with hc
    set d : ℤ := γ 1 1 with hd
    have hdet : a * d - b * c = 1 := by
      have := γ.2
      rwa [Matrix.det_fin_two] at this
    have hdetc : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
    have hden : ((c : ℂ) * z + d) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero γ z
      rwa [ModularGroup.denom_apply] at this
    have hwval : ((γ • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [algebraMap_int_eq, ← ha, ← hb, ← hc, ← hd]
    have hw' : ((c : ℂ) * z + d) * ((γ • z : ℍ) : ℂ) = (a : ℂ) * z + b := by
      rw [hwval, mul_comm, div_mul_cancel₀ _ hden]
    refine ⟨(Units.mk0 _ hden)⁻¹, ?_⟩
    ext x
    rw [PeriodPair.mem_smul_lattice]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, n, hmn⟩ := mem_periodPair_lattice.mp hy
      refine mem_periodPair_lattice.mpr ⟨m * a - n * b, n * d - m * c, ?_⟩
      rw [show ((Units.mk0 _ hden)⁻¹ : ℂˣ).val = ((c : ℂ) * z + d)⁻¹ from rfl, ← hmn,
        eq_inv_mul_iff_mul_eq₀ hden]
      push_cast
      linear_combination ((n : ℂ) * d - m * c) * hw' + ((m : ℂ) + n * z) * hdetc
    · intro hx
      obtain ⟨m, n, hmn⟩ := mem_periodPair_lattice.mp hx
      refine ⟨((c : ℂ) * z + d) * x, mem_periodPair_lattice.mpr
        ⟨m * d + n * b, m * c + n * a, ?_⟩, by
          rw [show ((Units.mk0 _ hden)⁻¹ : ℂˣ).val = ((c : ℂ) * z + d)⁻¹ from rfl]
          rw [inv_mul_cancel_left₀ hden]⟩
      rw [← hmn]
      push_cast
      linear_combination (-(n : ℂ)) * hw'

end Sl2Homothety

/-- The quotient of the upper half-plane by the usual `SL(2, ℤ)` action. -/
abbrev ModularOrbit :=
  MulAction.orbitRel.Quotient (SL(2, ℤ)) ℍ

/-- The `j`-function descends to the quotient by `SL(2, ℤ)`. -/
noncomputable def modularJ : ModularOrbit → ℂ :=
  Quotient.lift j fun z w hzw => by
    have hzw' : MulAction.orbitRel (SL(2, ℤ)) ℍ z w := hzw
    rw [MulAction.orbitRel_apply] at hzw'
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hzw'
    rw [← hγ]
    exact j_invariant γ w

@[simp]
theorem modularJ_mk (z : ℍ) :
    modularJ (Quotient.mk (MulAction.orbitRel (SL(2, ℤ)) ℍ) z) = j z :=
  rfl

/-- The classical injectivity assertion for `j`: after quotienting by `SL(2, ℤ)`,
the descended map is injective. -/
def JInjectiveUpToSL2Z : Prop :=
  Function.Injective modularJ

/-- The proved easy direction: points in the same `SL(2, ℤ)`-orbit have the same `j`-value. -/
theorem j_eq_of_exists_sl2_smul_eq {z w : ℍ}
    (h : ∃ γ : SL(2, ℤ), γ • z = w) : j z = j w := by
  obtain ⟨γ, rfl⟩ := h
  exact (j_invariant γ z).symm

/-- The quotient-level injectivity assertion is equivalent to the pointwise orbit statement. -/
theorem jInjectiveUpToSL2Z_iff :
    JInjectiveUpToSL2Z ↔
      ∀ z w : ℍ, j z = j w → ∃ γ : SL(2, ℤ), γ • z = w := by
  constructor
  · intro hinj z w hjw
    have hq :
        (Quotient.mk (MulAction.orbitRel (SL(2, ℤ)) ℍ) z : ModularOrbit) =
          Quotient.mk (MulAction.orbitRel (SL(2, ℤ)) ℍ) w := by
      apply hinj
      simpa using hjw
    have hrel : MulAction.orbitRel (SL(2, ℤ)) ℍ z w := Quotient.exact hq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm, MulAction.mem_orbit_iff] at hrel
    exact hrel
  · intro h q r hqr
    refine Quotient.inductionOn₂ q r ?_ hqr
    intro z w hzw
    obtain ⟨γ, hγ⟩ := h z w (by simpa using hzw)
    apply Quotient.sound
    change MulAction.orbitRel (SL(2, ℤ)) ℍ z w
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
    exact MulAction.mem_orbit_iff.mpr ⟨γ, hγ⟩

/-- Assuming the uniformisation/classification input above, the modular `j`-function separates
`SL(2, ℤ)`-orbits. -/
theorem j_eq_iff_exists_sl2_smul_eq (z w : ℍ) :
    j z = j w ↔ ∃ γ : SL(2, ℤ), γ • z = w := by
  constructor
  · intro hj
    have hJ :
        (UpperHalfPlane.periodPair z).j =
          (UpperHalfPlane.periodPair w).j := by
      rw [← j_eq_periodPair_j z, ← j_eq_periodPair_j w]
      exact hj
    exact periodPair_homothetic_iff_exists_sl2_smul_eq.mp
      (PeriodPair.homothetic_of_j_eq hJ)
  · exact fun h => j_eq_of_exists_sl2_smul_eq h
