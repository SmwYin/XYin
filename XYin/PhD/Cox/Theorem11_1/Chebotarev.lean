/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevAbelianRatio
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevDensity
import XYin.PhD.Cox.Theorem11_1.ChebotarevFixedField
import XYin.PhD.Cox.Theorem11_1.ChebotarevCrossing
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Chebotarev density and infinitude endpoints

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Planning source: Abelian.lean:853; statement placeholder. -/
theorem liminf_density_S_sigma_ge_card_H_n_div_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
        / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set Sσ : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hSσ
  set c : ℝ := (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹ with hc
  obtain ⟨S, hpd, hsub, hd⟩ := exists_cyclotomicCrossing_fibres K L σ m _hm hm4 hcop
  have : Fintype {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Fintype.ofFinite _
  set t : Finset {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Finset.univ with ht
  have hpd' : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S := by
    rw [ht, Finset.coe_univ]; exact hpd
  have hUdens : HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) :=
    hasDirichletDensity_biUnion_const t S c hpd' fun i _ ↦ hd i
  have hUsub : (⋃ i ∈ t, S i) ⊆ Sσ := Set.iUnion₂_subset fun i _ ↦ hsub i
  have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := hUdens.hasLower
  have hSσlow : HasLowerDirichletDensity Sσ
      (Filter.liminf
        (fun s : ℝ ↦ primeIdealZetaSum Sσ s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
        (𝓝[>] 1)) := rfl
  have hmono := HasLowerDirichletDensity.mono K hUsub hUlow hSσlow
  have htcard : (t.card : ℝ) • c
      = (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
          / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ)) := by
    rw [ht, Finset.card_univ, hc, smul_eq_mul, ← Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [htcard] at hmono
  exact hmono

/-- Planning source: Abelian.lean:1296; statement placeholder. -/
theorem exists_admissible_prime (n d : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    ∃ m : ℕ, m.Prime ∧ d < m ∧ m % 4 ≠ 2 ∧ n ^ k ∣ m - 1 := by
  obtain ⟨m, hmp, hmgt, hmeq⟩ := Nat.exists_prime_gt_modEq_one (k := 4 * n ^ k) (max d 1)
    (by positivity)
  have hdvd : 4 * n ^ k ∣ m - 1 := (Nat.modEq_iff_dvd' hmp.one_lt.le).mp hmeq.symm
  refine ⟨m, hmp, by omega, ?_, dvd_trans ⟨4, by ring⟩ hdvd⟩
  have := dvd_trans ⟨n ^ k, rfl⟩ hdvd
  omega

/-- Planning source: Abelian.lean:1309; statement placeholder. -/
theorem liminf_ratio_ge_inv_card_G
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    (Nat.card Gal(L/K) : ℝ)⁻¹
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set n : ℕ := Nat.card Gal(L/K) with hn
  set L_inf : ℝ :=
    Filter.liminf
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) with hLinf
  have hnpos : 0 < n := hn ▸ Nat.card_pos
  have hn1 : 1 ≤ n := hnpos
  set dB : ℕ := (NumberField.discr L).natAbs with hdB
  have hdBpos : 0 < dB := by
    rw [hdB, Int.natAbs_pos]
    exact NumberField.discr_ne_zero L
  choose m hmp hmgt hm4 hmdvd using exists_admissible_prime n dB hn1
  have hm1 : ∀ k, 1 ≤ m k := fun k ↦ (hmp k).one_lt.le
  have hmne : ∀ k, m k ≠ 0 := fun k ↦ (hmp k).pos.ne'
  have hmNeZero : ∀ k, NeZero (m k) := fun k ↦ ⟨hmne k⟩
  have hmcop : ∀ k, dB.Coprime (m k) := fun k ↦ by
    rw [Nat.coprime_comm, (hmp k).coprime_iff_not_dvd]
    exact fun hdvd ↦ absurd (Nat.le_of_dvd hdBpos hdvd) (Nat.not_le.mpr (hmgt k))
  have hexp : ∀ k, Monoid.exponent (ZMod (m k))ˣ = m k - 1 := fun k ↦ by
    haveI : Fact (m k).Prime := ⟨hmp k⟩
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (hmp k)]
  have hbound : ∀ k : ℕ,
      (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹ ≤ L_inf := by
    intro k
    have hbnd := liminf_density_S_sigma_ge_card_H_n_div_GH K L σ (m k) (hm1 k) (hm4 k)
      (hdB ▸ hmcop k)
    rw [← hn, ← hLinf] at hbnd
    refine le_trans (le_of_eq ?_) hbnd
    have hHpos : (0 : ℝ) < Nat.card ((ZMod (m k))ˣ) := by
      have := hmNeZero k
      exact_mod_cast Nat.card_pos
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    field_simp
  have hexpdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors,
      p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ := fun k _ p hp ↦ by
    rw [hexp k]
    refine dvd_trans ?_ (hmdvd k)
    calc p ^ (k * n.factorization p) = (p ^ n.factorization p) ^ k := by rw [← pow_mul, mul_comm]
      _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
  have htends : Filter.Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹)
      Filter.atTop (𝓝 ((n : ℝ)⁻¹)) := by
    simpa using
      (ratio_card_dvd_orderOf_tendsto_one n hn1 m hmNeZero hexpdvd).mul_const ((n : ℝ)⁻¹)
  exact le_of_tendsto htends (Filter.Eventually.of_forall hbound)

/-- Planning source: Abelian.lean:1379; statement placeholder. -/
theorem ratioSum_frobeniusFibres_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] :
    Filter.Tendsto
      (fun s : ℝ ↦ ∑ σ : Gal(L/K),
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  classical
  set S : Gal(L/K) → Set (Ideal (𝓞 K)) := fun σ ↦
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hS
  set R : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
  set D : ℝ → ℝ := primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) with hD
  letI : CommMonoid Gal(L/K) := IsMulCommutative.instCommMonoid
  have hmk_inj : Function.Injective (ConjClasses.mk : Gal(L/K) → ConjClasses Gal(L/K)) :=
    ConjClasses.mk_injective
  have hpd : ((Finset.univ : Finset Gal(L/K)) : Set Gal(L/K)).PairwiseDisjoint S := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun 𝔭 ha hb ↦ hab (hmk_inj ?_)
    rw [hS] at ha hb
    exact ha.2.2.symm.trans hb.2.2
  have hdisjR : Disjoint (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) R := by
    refine Set.disjoint_left.mpr fun 𝔭 hmem hbad ↦ ?_
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    exact hbad.2.2 (hS ▸ hσ).2.1
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔭 ∈ (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) ∪ R := by
    intro 𝔭 hp hne
    by_cases hunr : UnramifiedIn K L 𝔭
    · obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (frobeniusClass K L 𝔭)
      exact Or.inl <| Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨Finset.mem_univ σ,
        hS ▸ ⟨hp, hunr, hσ.symm⟩⟩⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  have hR0 : Filter.Tendsto (fun s ↦ primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 0) :=
    hasDirichletDensity_of_finite K hRfin
  have hDpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < D s :=
    (primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0
  have hcomp : Filter.Tendsto (fun s ↦ 1 - primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 1) := by
    simpa using hR0.const_sub 1
  refine hcomp.congr' ?_
  filter_upwards [hDpos, self_mem_nhdsWithin] with s hpos hs1
  simp only [Set.mem_Ioi] at hs1
  have hsum : ∑ σ : Gal(L/K), primeIdealZetaSum (S σ) s
      = primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s :=
    (primeIdealZetaSum_biUnion_of_pairwiseDisjoint K Finset.univ S hpd hs1).symm
  have hadd : primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s
      + primeIdealZetaSum R s = D s := by
    rw [← primeIdealZetaSum_union_of_disjoint K hdisjR hs1, hD]
    exact primeIdealZetaSum_eq_univ_of_forall_prime_mem K hcover s
  rw [← Finset.sum_div, hsum]
  field_simp
  linarith [hadd]

/-- The zeta-sum ratio is eventually bounded below by zero (AINTLIB Abelian.lean:1561). -/
theorem isBoundedUnder_ge_ratio_zetaSum (T : Set (Ideal (𝓞 K))) :
    Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ))
      (fun s ↦ primeIdealZetaSum T s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s) :=
  isBoundedUnder_of_eventually_ge (a := 0)
    (Filter.Eventually.of_forall fun s ↦
      div_nonneg (primeIdealZetaSum_nonneg K _ s) (primeIdealZetaSum_nonneg K _ s))

/-- Planning source: Abelian.lean:1580; statement placeholder. -/
theorem chebotarev_abelian
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk τ} s
        / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
    (fun τ ↦ ?_) (fun τ ↦ isBoundedUnder_ge_ratio_zetaSum K _)
    (ratioSum_frobeniusFibres_tendsto_one K L) σ
  simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ

/-- Planning source: Main.lean:70; statement placeholder. -/
theorem chebotarev_density
    [FiniteDimensional K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  let e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  have : IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul e x y, ← map_mul e y x, mul_comm' x y]
  exact density_lift_through_fixedField K L σ
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    (e ⟨σ, Subgroup.mem_zpowers σ⟩) rfl rfl
    (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))

/-- Planning source: Main.lean:127; statement placeholder. -/
theorem infinite_setOf_frobenius_class
    (C : ConjClasses Gal(L/K)) :
    Set.Infinite
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C} := by
  refine infinite_of_hasDirichletDensity_pos K (chebotarev_density K L C) ?_
  apply div_pos
  · exact_mod_cast ConjClasses_carrier_card_pos C
  · exact_mod_cast Nat.card_pos (α := Gal(L/K))

end Cox.Chebotarev
