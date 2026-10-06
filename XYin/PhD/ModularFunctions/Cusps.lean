/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.GrowthAtCusp
import XYin.PhD.ModularFunctions.NormalFormGrowth
import XYin.PhD.ModularFunctions.NormalFormSlash
import XYin.PhD.ModularFunctions.CuspPeriod

/-!
# Meromorphy at cusps and exponential growth

For canonical meromorphic representatives, a uniform exponential bound is equivalent to
meromorphy in any positive-period q-coordinate. The normal-form hypothesis rules out arbitrary
exceptional values accumulating at a cusp. For slash-invariant forms on discrete groups with
determinants in `{±1}`, the required positive periods follow from the cusp condition.
-/

open UpperHalfPlane Function
open scoped MatrixGroups ModularForm

namespace UpperHalfPlane

/-- For normal meromorphic functions, finite exponential growth is precisely meromorphy at
infinity in any positive-period cusp parameter. -/
theorem isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn
    {f : ℍ → ℂ} (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    {h : ℝ} (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) :
    IsOfExponentialGrowth f ↔ MeromorphicAt (cuspFunction h f) 0 :=
  ⟨fun hb ↦ (isOfExponentialGrowth_iff_meromorphicAt_cuspFunction hh hper
      (eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound hf hb)).mp hb,
    isOfExponentialGrowth_of_meromorphicAt_cuspFunction hh hper⟩

/-- The reciprocal of a periodic meromorphic function in normal form with exponential growth has
exponential growth. -/
theorem IsOfExponentialGrowth.inv {f : ℍ → ℂ} (hf : IsOfExponentialGrowth f)
    (hNF : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) {h : ℝ} (hh : 0 < h)
    (hper : Periodic (f ∘ ofComplex) h) : IsOfExponentialGrowth f⁻¹ := by
  have hmer := (isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn hNF hh
    hper).1 hf
  have hper' : Periodic (f⁻¹ ∘ ofComplex) h := fun z ↦ by
    simpa using congrArg Inv.inv (hper z)
  refine isOfExponentialGrowth_of_meromorphicAt_cuspFunction hh hper' (hmer.inv.congr ?_)
  filter_upwards [self_mem_nhdsWithin] with q (hq : q ≠ 0)
  simp only [cuspFunction, Pi.inv_apply, Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  rfl

end UpperHalfPlane

namespace OnePoint

/-- A weight-zero function is meromorphic at a cusp if each scaling transform is periodic
with a positive period and its associated cusp function is meromorphic at zero. -/
def IsMeromorphicAt (c : OnePoint ℝ) (f : ℍ → ℂ) : Prop :=
  ∀ g : GL (Fin 2) ℝ, g • ∞ = c →
    ∃ h : ℝ, 0 < h ∧ Periodic ((f ∣[(0 : ℤ)] g) ∘ ofComplex) h ∧
      MeromorphicAt (cuspFunction h (f ∣[(0 : ℤ)] g)) 0

lemma IsMeromorphicAt.smul_iff {c : OnePoint ℝ} {f : ℍ → ℂ} {g : GL (Fin 2) ℝ} :
    IsMeromorphicAt (g • c) f ↔ IsMeromorphicAt c (f ∣[(0 : ℤ)] g) := by
  rw [IsMeromorphicAt, IsMeromorphicAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

/-- A function whose integral transforms are all periodic with a common positive period and
meromorphic at the cusp has exponential growth at every cusp of `SL₂(ℤ)`. -/
theorem isOfExponentialGrowthAt_of_forall_sl2 {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hper : ∀ γ : SL(2, ℤ), Periodic ((fun τ ↦ f (γ • τ)) ∘ ofComplex) h)
    (hcusp : ∀ γ : SL(2, ℤ), MeromorphicAt (cuspFunction h (fun τ ↦ f (γ • τ))) 0)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsOfExponentialGrowthAt f :=
  isOfExponentialGrowthAt_of_forall_SL2Z (fun γ ↦ by
    rw [ModularForm.SL_slash_zero_eq]
    exact isOfExponentialGrowth_of_meromorphicAt_cuspFunction hh (hper γ) (hcusp γ)) hc

/-- The growth criterion agrees with meromorphy in any chosen periodic cusp chart. -/
theorem isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction
    {c : OnePoint ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    {g : GL (Fin 2) ℝ} (hg : g • ∞ = c) {h : ℝ} (hh : 0 < h)
    (hper : Periodic ((f ∣[(0 : ℤ)] g) ∘ ofComplex) h) :
    c.IsOfExponentialGrowthAt f ↔ MeromorphicAt (cuspFunction h (f ∣[(0 : ℤ)] g)) 0 :=
  (isOfExponentialGrowthAt_iff hg).trans
    (isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn
      (meromorphicNFOn_slash_zero hf g) hh hper)

/-- For a canonical slash-invariant meromorphic function, exponential growth and meromorphy
at a cusp are equivalent. The group assumptions ensure positive periods in cusp charts. -/
theorem isOfExponentialGrowthAt_iff_isMeromorphicAt
    {Γ : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ 0)
    (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsOfExponentialGrowthAt f ↔ c.IsMeromorphicAt f := by
  constructor
  · intro hb g hg
    obtain ⟨h, hh, hper⟩ := f.exists_pos_period_at_cusp hc g hg
    exact ⟨h, hh, hper,
      (isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction hf hg hh hper).mp hb⟩
  · intro hm g hg
    obtain ⟨h, hh, hper, hmer⟩ := hm g hg
    exact isOfExponentialGrowth_of_meromorphicAt_cuspFunction hh hper hmer

/-- The weight-zero exponential cusp condition is meromorphy in any positive-period
q-coordinate. -/
theorem isExpBoundedAt_zero_iff_meromorphicAt_cuspFunction
    {c : OnePoint ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    {g : GL (Fin 2) ℝ} (hg : g • ∞ = c) {h : ℝ} (hh : 0 < h)
    (hper : Periodic ((f ∣[(0 : ℤ)] g) ∘ ofComplex) h) :
    c.IsExpBoundedAt f 0 ↔ MeromorphicAt (cuspFunction h (f ∣[(0 : ℤ)] g)) 0 :=
  IsExpBoundedAt.iff_at_zero.trans
    (isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction hf hg hh hper)

/-- For a canonical slash-invariant function on a discrete group with determinants in `{±1}`,
the period-free weight-zero exponential condition equals the usual meromorphic cusp condition. -/
theorem isExpBoundedAt_zero_iff_isMeromorphicAt
    {Γ : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ 0)
    (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsExpBoundedAt f 0 ↔ c.IsMeromorphicAt f :=
  IsExpBoundedAt.iff_at_zero.trans (isOfExponentialGrowthAt_iff_isMeromorphicAt f hf hc)

/-- The reciprocal of a canonical slash-invariant meromorphic function with exponential growth
at a cusp has exponential growth at that cusp. The group assumptions ensure positive periods in
cusp charts. -/
theorem IsOfExponentialGrowthAt.inv
    {Γ : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ 0)
    (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) (hgrowth : c.IsOfExponentialGrowthAt f) :
    c.IsOfExponentialGrowthAt (f : ℍ → ℂ)⁻¹ := fun g hg ↦ by
  obtain ⟨h, hh, hper⟩ := f.exists_pos_period_at_cusp hc g hg
  rw [ModularForm.inv_slash_zero]
  exact ((hgrowth g hg).inv (meromorphicNFOn_slash_zero hf g) hh hper).smul _

end OnePoint

namespace SlashInvariantForm

/-- The period-free growth condition at all cusps is equivalent to meromorphy at all cusps. -/
theorem exponential_growth_at_cusps_iff
    {Γ : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ 0)
    (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet) :
    (∀ c, IsCusp c Γ → c.IsOfExponentialGrowthAt f) ↔
      ∀ c, IsCusp c Γ → c.IsMeromorphicAt f :=
  forall_congr' fun _ ↦ forall_congr' fun hc ↦
    OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt f hf hc

/-- The modular-function cusp field can equivalently be given by the usual q-coordinate
meromorphy condition. -/
theorem exp_bounded_at_cusps_zero_iff
    {Γ : Subgroup (GL (Fin 2) ℝ)} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ 0)
    (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet) :
    (∀ c, IsCusp c Γ → c.IsExpBoundedAt f 0) ↔
      ∀ c, IsCusp c Γ → c.IsMeromorphicAt f :=
  forall_congr' fun _ ↦ forall_congr' fun hc ↦
    OnePoint.isExpBoundedAt_zero_iff_isMeromorphicAt f hf hc

end SlashInvariantForm
