import XYin.jFunction.jLevelN
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
  have h1 : Delta z = (ModForm_mk _ _ Delta_E4_E6_aux) z := by
    rw [Delta_E4_eqn]; rfl
  rw [h1, Delta_E4_E6_eq]
  have hds : (((DirectSum.of (ModularForm Γ(1)) 4) _root_.E₄ ^ 3) 12) =
      _root_.E₄.mul (_root_.E₄.mul _root_.E₄) := by
    rw [pow_three, DirectSum.of_mul_of, DirectSum.of_mul_of]
    change (((DirectSum.of (ModularForm Γ(1)) 12)
        (GradedMonoid.GMul.mul _root_.E₄ (GradedMonoid.GMul.mul _root_.E₄ _root_.E₄))) 12) = _
    rw [DirectSum.of_eq_same]; rfl
  have hd6 : ((DirectSum.of (ModularForm Γ(1)) 6) _root_.E₆ ^ 2) 12 =
      _root_.E₆.mul _root_.E₆ := by
    rw [pow_two, DirectSum.of_mul_of]
    change (((DirectSum.of (ModularForm Γ(1)) 12)
        (GradedMonoid.GMul.mul _root_.E₆ _root_.E₆)) 12) = _
    rw [DirectSum.of_eq_same]; rfl
  have hds' : (((DirectSum.of (ModularForm Γ(1)) 4) _root_.E₄ ^ 3) 12) z =
      E4 z * (E4 z * E4 z) := by
    rw [hds]; rfl
  have hd6' : (((DirectSum.of (ModularForm Γ(1)) 6) _root_.E₆ ^ 2) 12) z = E6 z * E6 z := by
    rw [hd6]; rfl
  simp only [DirectSum.sub_apply, ModularForm.IsGLPos.smul_apply, ModularForm.sub_apply,
    smul_eq_mul, hds', hd6']
  ring

private lemma Delta_ne_zero_apply (z : ℍ) : Delta z ≠ 0 := by
  rw [Delta_apply]
  exact Δ_ne_zero z

private lemma E4_E6_sub_ne_zero (z : ℍ) : E4 z ^ 3 - E6 z ^ 2 ≠ 0 := by
  intro h
  apply Delta_ne_zero_apply z
  rw [Delta_eq_E4_E6, h, zero_div]

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
    refine ⟨Units.mk0 c hc0, invariantsDetermineLattice _ _ ?_ ?_⟩
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
      refine ⟨Units.mk0 c hc0, invariantsDetermineLattice _ _ ?_ ?_⟩
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
      refine ⟨Units.mk0 c hc0, invariantsDetermineLattice _ _ ?_ ?_⟩
      · rw [g₂_smul]
        rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc4]
        field_simp
      · rw [g₃_smul]
        rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc6]
        field_simp

end PeriodPair

/-- Homothety of normalized upper-half-plane lattices is equivalent to equality modulo the usual
`SL(2, ℤ)` action. -/
theorem periodPair_homothetic_iff_exists_sl2_smul_eq {z w : ℍ} :
    PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w) ↔
      ∃ γ : SL(2, ℤ), γ • z = w := by
  sorry

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
