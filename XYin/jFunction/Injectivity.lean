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

/-- Uniformisation/classification input: the `j`-invariant classifies complex period lattices up
to homothety. -/
theorem homothetic_of_j_eq {L M : PeriodPair} (h : L.j = M.j) : L.Homothetic M := by
  sorry

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
