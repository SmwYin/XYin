/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalComparison
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalCyclotomic
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

/-! # Janusz V.11.1–11.2: the decomposition-group image

The erased ray-principal Artin elements generate the decomposition group of a prime of an
abelian extension. They lie in it because they act trivially on the decomposition field. A
proper subgroup of prime index containing them is impossible: cyclotomic base change and the
paired class field force the prime below to split in the corresponding fixed field, which
contradicts the uniqueness of the prime above in the decomposition field. The conductor
support theorem is not assumed.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNF_K : NumberField K]
variable (L : Type*) [Field L] [hNF_L : NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

/-- The erased principal-ideal map used in Janusz V.(11.1). -/
def rayArtinMap (m : Ideal (𝓞 K)) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L)) :
    rayElements K m →* (L ≃ₐ[K] L) :=
  (φ.comp (eraseModulusFactors K (v.asIdeal ^ a * m))).comp
    ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype)

-- The unused hypotheses are kept: the planned signature includes them.
set_option linter.unusedVariables false in
include hNF_K in
/-- In V.11.2 the erased part of a ray principal is supported only at the chosen prime. -/
theorem erased_ray_principal_quotient_mem_primeSupport (m : Ideal (𝓞 K))
    (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ) (ha : 0 < a)
    (u : Kˣ) (hu : u ∈ rayElements K m) :
    toPrincipalIdeal (𝓞 K) K u *
      (eraseModulusFactors K (v.asIdeal ^ a * m)
        (toPrincipalIdeal (𝓞 K) K u) : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈
          modulusSupportedIdeals K v.asIdeal := by
  have hspec := eraseModulusFactors_spec K (v.asIdeal ^ a * m) (toPrincipalIdeal (𝓞 K) K u)
  have huc : toPrincipalIdeal (𝓞 K) K u ∈ coprimeIdeals K m :=
    principal_mem_coprime_of_mem_rayElements K m u hu
  have hEc := (eraseModulusFactors K (v.asIdeal ^ a * m) (toPrincipalIdeal (𝓞 K) K u)).2
  rw [mem_modulusSupportedIdeals_iff_count_eq_zero] at hspec ⊢
  intro w hw
  by_cases hNw : v.asIdeal ^ a * m ≤ w.asIdeal
  · have hmw : m ≤ w.asIdeal := by
      rcases w.isPrime.mul_le.mp hNw with h | h
      · exact absurd (w.isPrime.le_of_pow_le h) hw
      · exact h
    rw [Units.val_mul, Units.val_inv_eq_inv_val, FractionalIdeal.count_mul K w (Units.ne_zero _)
      (inv_ne_zero (Units.ne_zero _)), FractionalIdeal.count_inv,
      (mem_coprimeIdeals_iff_count_eq_zero K m _).mp huc w hmw,
      (mem_coprimeIdeals_iff_count_eq_zero K _ _).mp hEc w hNw, neg_zero, add_zero]
  · exact hspec w hNw

include hNF_K in
/-- The subgroup supported on a single prime is the group of its integral powers. -/
theorem modulusSupportedIdeals_prime_eq_zpowers
    (P : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hP : (P : FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal) :
    modulusSupportedIdeals K v.asIdeal = Subgroup.zpowers P := by
  have hPmem : P ∈ modulusSupportedIdeals K v.asIdeal := Subgroup.subset_closure ⟨v, le_rfl, hP⟩
  have hPc := (mem_modulusSupportedIdeals_iff_count_eq_zero K v.asIdeal P).mp hPmem
  apply le_antisymm
  · intro x hx
    have hxc := (mem_modulusSupportedIdeals_iff_count_eq_zero K v.asIdeal x).mp hx
    have h1 : x * (P ^ FractionalIdeal.count K v (x : FractionalIdeal (𝓞 K)⁰ K))⁻¹ = 1 := by
      apply fractionalIdealUnit_eq_one_of_count_eq_zero
      intro w
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
        FractionalIdeal.count_mul K w (Units.ne_zero x)
          (inv_ne_zero (zpow_ne_zero _ (Units.ne_zero P))), FractionalIdeal.count_inv,
        FractionalIdeal.count_zpow]
      by_cases hw : v.asIdeal ≤ w.asIdeal
      · have hwv : w = v := (HeightOneSpectrum.ext
          ((v.isPrime.isMaximal v.ne_bot).eq_of_le w.isPrime.ne_top hw)).symm
        subst hwv
        rw [hP, FractionalIdeal.count_self, mul_one, add_neg_cancel]
      · rw [hxc w hw, hPc w hw, mul_zero, neg_zero, add_zero]
    exact ⟨_, (mul_inv_eq_one.mp h1).symm⟩
  · exact Subgroup.zpowers_le.mpr hPmem

include hNF_K in
/-- The source factorization j((u))=p^(-r)(u), with an actual integer exponent. -/
theorem erased_ray_principal_eq_prime_zpow (m : Ideal (𝓞 K))
    (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ) (ha : 0 < a)
    (P : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hP : (P : FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal)
    (u : Kˣ) (hu : u ∈ rayElements K m) :
    ∃ r : ℤ,
      (eraseModulusFactors K (v.asIdeal ^ a * m)
        (toPrincipalIdeal (𝓞 K) K u) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          P ^ r * toPrincipalIdeal (𝓞 K) K u := by
  have h := erased_ray_principal_quotient_mem_primeSupport K v m hcop a ha u hu
  rw [modulusSupportedIdeals_prime_eq_zpowers K v P hP] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine ⟨-k, ?_⟩
  rw [zpow_neg, hk, mul_inv_rev, inv_inv, inv_mul_cancel_right]

/-- A maximal proper subgroup gives a simple quotient (normality is explicit). -/
theorem isSimpleGroup_quotient_of_isCoatom {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (hH : IsCoatom H) : IsSimpleGroup (G ⧸ H) := by
  haveI : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH.1
  refine { eq_bot_or_eq_top_of_normal := fun N _ => ?_ }
  rcases eq_or_lt_of_le (QuotientGroup.le_comap_mk' H N) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    have hg : g ∈ N.comap (QuotientGroup.mk' H) := hx
    rw [← h] at hg
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
    have hg : g ∈ N.comap (QuotientGroup.mk' H) := by
      rw [hH.2 _ h]
      exact Subgroup.mem_top g
    exact hg

/-- A finite simple abelian quotient has prime cardinality. -/
theorem index_prime_of_isCoatom {G : Type*} [Group G] [IsMulCommutative G]
    (H : Subgroup G) (hH : IsCoatom H) : Nat.Prime H.index := by
  haveI : H.Normal := ⟨fun n hn g => by
    have hc : g * n = n * g := (inferInstance : IsMulCommutative G).is_comm.comm g n
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  haveI := isSimpleGroup_quotient_of_isCoatom H hH
  haveI : IsMulCommutative (G ⧸ H) := ⟨⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (inferInstance : IsMulCommutative G).is_comm.comm x y]⟩⟩
  exact Group.is_simple_iff_prime_card.mp inferInstance

/-- A covering subgroup pair becomes a maximal proper subgroup inside the upper group. -/
theorem isCoatom_subgroupOf_of_covBy {G : Type*} [Group G]
    (H D : Subgroup G) (hHD : H ⋖ D) : IsCoatom (H.subgroupOf D) := by
  obtain ⟨hlt, hcov⟩ := hHD
  refine ⟨fun htop => ?_, fun K' hK' => ?_⟩
  · rw [Subgroup.subgroupOf_eq_top] at htop
    exact hlt.not_ge htop
  · have hmap : (H.subgroupOf D).map D.subtype = H := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hlt.le]
    have hlt' : H < K'.map D.subtype := by
      rw [← hmap]
      exact (Subgroup.map_lt_map_iff_of_injective D.subtype_injective).mpr hK'
    have heq : K'.map D.subtype = D := by
      by_contra hne
      exact hcov hlt' (lt_of_le_of_ne (Subgroup.map_subtype_le K') hne)
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ K'.map D.subtype := by
      rw [heq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy

/-- A prime-index overgroup of any proper subgroup of a finite abelian group. -/
theorem exists_prime_relIndex_overgroup {G : Type*} [Group G] [IsMulCommutative G] [Finite G]
    (H D : Subgroup G) (hHD : H < D) :
    ∃ G₀ : Subgroup G, H ≤ G₀ ∧ G₀ < D ∧ Nat.Prime (G₀.relIndex D) := by
  obtain ⟨G₀, hHG₀, hcov⟩ := exists_le_covBy_of_lt hHD
  haveI : IsMulCommutative D :=
    ⟨⟨fun a b => Subtype.ext ((inferInstance : IsMulCommutative G).is_comm.comm (a : G) b)⟩⟩
  exact ⟨G₀, hHG₀, hcov.lt,
    index_prime_of_isCoatom (G₀.subgroupOf D) (isCoatom_subgroupOf_of_covBy G₀ D hcov)⟩

/-- The numeric coprime-degree step on printed p.186. -/
theorem eq_one_of_dvd_prime_and_pred {q n : ℕ} (hq : q.Prime)
    (hnq : n ∣ q) (hnpred : n ∣ q - 1) : n = 1 := by
  rcases hq.eq_one_or_self_of_dvd n hnq with h | h
  · exact h
  · subst h
    have h1 : 0 < n - 1 := Nat.sub_pos_of_lt hq.one_lt
    have := Nat.le_of_dvd h1 hnpred
    omega

/-- The actual decomposition field of the chosen upper prime. -/
def decompositionSubfield : IntermediateField K L :=
  IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)

include hNF_K hNF_L in
/-- Above the contracted prime of the decomposition field there is a unique prime of L. -/
theorem decompositionSubfield_unique_prime [IsGalois K L] :
    Subsingleton ((w.asIdeal.under (𝓞 (decompositionSubfield K L w))).primesOver (𝓞 L)) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsGalois (decompositionSubfield K L w) L := IsGalois.tower_top_intermediateField _
  haveI : IsGaloisGroup Gal(L/(decompositionSubfield K L w)) (decompositionSubfield K L w) L :=
    IsGaloisGroup.of_isGalois _ L
  haveI : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 (decompositionSubfield K L w))) :=
    Ideal.over_under (A := 𝓞 (decompositionSubfield K L w)) (P := w.asIdeal)
  have key : ∀ P : Ideal (𝓞 L),
      P ∈ (w.asIdeal.under (𝓞 (decompositionSubfield K L w))).primesOver (𝓞 L) →
        P = w.asIdeal := by
    rintro P ⟨hPp, hPo⟩
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (w.asIdeal.under (𝓞 (decompositionSubfield K L w))) w.asIdeal P
      Gal(L/(decompositionSubfield K L w))
    have hmem : τ.restrictScalars K ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
      rw [← IntermediateField.fixingSubgroup_fixedField
        (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)]
      exact fun z => τ.commutes z
    rw [← hτ]
    exact MulAction.mem_stabilizer_iff.mp hmem
  exact ⟨fun P Q => Subtype.ext ((key P.1 P.2).trans (key Q.1 Q.2).symm)⟩

include hvw hNF_K hNF_L in
/-- In an abelian extension the base prime splits completely in its decomposition field. -/
theorem decompositionSubfield_splits [IsAbelianGalois K L] :
    v.asIdeal ∈ splittingIdeals K (decompositionSubfield K L w) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsAbelianGalois K (decompositionSubfield K L w) := IsAbelianGalois.tower_bot K _ L
  haveI : NumberField (decompositionSubfield K L w) := NumberField.of_module_finite K _
  haveI : IsGalois (decompositionSubfield K L w) L := IsGalois.tower_top_intermediateField _
  haveI : IsGaloisGroup Gal(L/K) K L := IsGaloisGroup.of_isGalois K L
  haveI : IsGaloisGroup Gal((decompositionSubfield K L w)/K) K (decompositionSubfield K L w) :=
    IsGaloisGroup.of_isGalois K _
  haveI : IsGaloisGroup Gal(L/(decompositionSubfield K L w)) (decompositionSubfield K L w) L :=
    IsGaloisGroup.of_isGalois _ L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (𝓞 K) (𝓞 (decompositionSubfield K L w)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (𝓞 (decompositionSubfield K L w)) (𝓞 L) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : IsDecompositionField K L w.asIdeal (decompositionSubfield K L w) :=
    inferInstanceAs (IsDecompositionField K L w.asIdeal
      (FixedPoints.intermediateField (MulAction.stabilizer Gal(L/K) w.asIdeal) :
        IntermediateField K L))
  have hrank : Module.finrank K (decompositionSubfield K L w) =
      (v.asIdeal.primesOver (𝓞 L)).ncard :=
    IsDecompositionField.rank_right (𝓞 K) K L w.asIdeal (decompositionSubfield K L w) v.ne_bot
  haveI hwZm : (w.asIdeal.under (𝓞 (decompositionSubfield K L w))).IsMaximal :=
    Ideal.IsMaximal.under (𝓞 (decompositionSubfield K L w)) w.asIdeal
  haveI : (w.asIdeal.under (𝓞 (decompositionSubfield K L w))).LiesOver v.asIdeal :=
    ⟨by rw [Ideal.under_under]; exact hvw.over⟩
  have hn := Ideal.ncard_primesOver_mul_ncard_primesOver
    (w.asIdeal.under (𝓞 (decompositionSubfield K L w)))
    Gal((decompositionSubfield K L w)/K) (𝓞 L) Gal(L/K) Gal(L/(decompositionSubfield K L w))
    v.ne_bot
  have hwmem : w.asIdeal ∈ (w.asIdeal.under (𝓞 (decompositionSubfield K L w))).primesOver (𝓞 L) :=
    ⟨w.isPrime, Ideal.over_under (A := 𝓞 (decompositionSubfield K L w)) (P := w.asIdeal)⟩
  have hone : ((w.asIdeal.under (𝓞 (decompositionSubfield K L w))).primesOver (𝓞 L)).ncard = 1 := by
    haveI := decompositionSubfield_unique_prime K L w
    rw [Set.ncard_eq_one]
    refine ⟨w.asIdeal, Set.eq_singleton_iff_unique_mem.mpr ⟨hwmem, fun P hP => ?_⟩⟩
    exact congrArg Subtype.val (Subsingleton.elim (⟨P, hP⟩ :
      ((w.asIdeal.under (𝓞 (decompositionSubfield K L w))).primesOver (𝓞 L))) ⟨_, hwmem⟩)
  rw [hone, mul_one] at hn
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.ne_bot
    (𝓞 (decompositionSubfield K L w)) Gal((decompositionSubfield K L w)/K)
  rw [IsGalois.card_aut_eq_finrank, hrank, ← hn] at hfund
  have hpos : 0 < (v.asIdeal.primesOver (𝓞 (decompositionSubfield K L w))).ncard := by
    have h0 : 0 < Module.finrank K (decompositionSubfield K L w) := Module.finrank_pos
    rw [hrank, ← hn] at h0
    exact h0
  have hef := Nat.eq_of_mul_eq_mul_left hpos (hfund.trans (mul_one _).symm)
  refine ⟨v.isPrime, v.ne_bot, fun P hP => ?_⟩
  obtain ⟨hPp, hPo⟩ := hP
  haveI := hPp
  haveI := hPo
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal((decompositionSubfield K L w)/K),
    ← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P Gal((decompositionSubfield K L w)/K)]
  exact ⟨Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- The fixed field of a smaller subgroup contains the decomposition field. -/
theorem decompositionSubfield_le_fixedField
    (G₀ : Subgroup (L ≃ₐ[K] L))
    (hG₀ : G₀ ≤ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    decompositionSubfield K L w ≤ IntermediateField.fixedField G₀ := by
  exact IntermediateField.fixedField_le hG₀

include hNF_K hNF_L in
/-- Prime relative index is exactly the prime extension degree over the decomposition field. -/
theorem finrank_fixedField_over_decompositionSubfield [IsGalois K L]
    (G₀ : Subgroup (L ≃ₐ[K] L))
    (hG₀ : G₀ ≤ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    letI := (IntermediateField.inclusion
      (decompositionSubfield_le_fixedField K L w G₀ hG₀)).toAlgebra
    Module.finrank (decompositionSubfield K L w) (IntermediateField.fixedField G₀) =
      G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
  letI := (IntermediateField.inclusion
    (decompositionSubfield_le_fixedField K L w G₀ hG₀)).toAlgebra
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsScalarTower (decompositionSubfield K L w) (IntermediateField.fixedField G₀) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := IntermediateField.finrank_fixedField_eq_card
    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
  have h2 := IntermediateField.finrank_fixedField_eq_card G₀
  have h3 := Module.finrank_mul_finrank (decompositionSubfield K L w)
    (IntermediateField.fixedField G₀) L
  have h4 : G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) * Nat.card G₀ =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
    rw [mul_comm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG₀).toEquiv]
    exact Subgroup.card_mul_index _
  rw [h2] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h3.trans (h1.trans h4.symm))

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
include hNF_K hNF_L in
/-- A split chosen prime may be removed from the support of an unramified modulus. -/
theorem isUnramifiedAway_remove_split_prime [IsGalois K L]
    (m : Ideal (𝓞 K)) (a : ℕ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hsplit : v.asIdeal ∈ splittingIdeals K L) : IsUnramifiedAway K m L := by
  intro q hq hq0 hqm P hP
  by_cases hqv : q = v.asIdeal
  · subst hqv
    exact (hsplit.2.2 P hP).1
  · have hvq : ¬v.asIdeal ≤ q := fun h =>
      hqv ((v.isPrime.isMaximal v.ne_bot).eq_of_le hq.ne_top h).symm
    have hqv' : q ⊔ v.asIdeal = ⊤ := by
      by_contra h
      exact hvq (le_sup_right.trans ((hq.isMaximal hq0).eq_of_le h le_sup_left).symm.le)
    have hqN : q ⊔ v.asIdeal ^ a * m = ⊤ := by
      rw [Ideal.sup_mul_eq_of_coprime_left (Ideal.sup_pow_eq_top hqv'), hqm]
    exact hU q hq hq0 hqN P hP

include hNF_K hNF_L in
/-- Reciprocity at a modulus without v and gcd of defining moduli remove the extra v-power. -/
theorem ray_kernel_remove_split_prime [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker)
    (ψ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hψ : IsArtinMap K m L ψ)
    (hU : IsUnramifiedAway K m L) : raySubgroup K m ≤ ψ.ker := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨S, hS⟩ := exists_modulus_support K m hm
  have hUS : IsUnramifiedAway K (supportModulus K S 1) L := by
    intro q hq hq0 hqS P hP
    refine hU q hq hq0 ?_ P hP
    by_contra hqm
    have hmq : m ≤ q :=
      le_sup_right.trans ((hq.isMaximal hq0).eq_of_le hqm le_sup_left).symm.le
    have hle : supportModulus K S 1 ≤ q :=
      (supportModulus_le_prime_iff K S 1 one_pos ⟨q, hq, hq0⟩).mpr ((hS _).mpr hmq)
    rw [sup_eq_left.mpr hle] at hqS
    exact hq.ne_top hqS
  obtain ⟨t₀, ht₀⟩ := artin_reciprocity_supported K L S hUS
  obtain ⟨t₁, ht₁⟩ := exists_supportModulus_le K m hm S (fun w hw => (hS w).mpr hw)
  have ht0 : 0 < max 1 (max t₀ t₁) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have htm : supportModulus K S (max 1 (max t₀ t₁)) ≤ m :=
    ht₁ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨χ, hχ, -, hχray⟩ := ht₀ _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hUt : IsUnramifiedAway K (supportModulus K S (max 1 (max t₀ t₁))) L :=
    fun q hq hq0 hqm => hU q hq hq0 (eq_top_mono (sup_le_sup_left htm q) hqm)
  have hχψ := isArtinMap_unique K _ L hUt hχ (isArtinMap_comp_inclusion K L htm ψ hψ)
  have hvm : v.asIdeal ^ a * m ≤ m := Ideal.mul_le_left
  have hvm0 : v.asIdeal ^ a * m ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) hm
  have hUv : IsUnramifiedAway K (v.asIdeal ^ a * m) L :=
    fun q hq hq0 hqm => hU q hq hq0 (eq_top_mono (sup_le_sup_left hvm q) hqm)
  have hφψ := isArtinMap_unique K _ L hUv hφ (isArtinMap_comp_inclusion K L hvm ψ hψ)
  have hamb : ∀ (n : Ideal (𝓞 K)) (hn : n ≤ m),
      (ψ.ker.comap (Subgroup.inclusion (coprimeIdeals_mono K hn))).map
        (coprimeIdeals K n).subtype =
          ψ.ker.map (coprimeIdeals K m).subtype ⊓ coprimeIdeals K n := by
    intro n hn
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨Subgroup.inclusion (coprimeIdeals_mono K hn) y, Subgroup.mem_comap.mp hy,
        Subgroup.coe_inclusion (coprimeIdeals_mono K hn) y⟩, y.2⟩
    · rintro ⟨⟨z, hz, hzx⟩, hxn⟩
      refine ⟨⟨x, hxn⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
      have hz' : Subgroup.inclusion (coprimeIdeals_mono K hn) ⟨x, hxn⟩ = z :=
        Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hzx.symm)
      rw [hz']
      exact hz
  have hray₁ : raySubgroup K (supportModulus K S (max 1 (max t₀ t₁))) ≤
      ψ.ker.comap (Subgroup.inclusion (coprimeIdeals_mono K htm)) := by
    rw [MonoidHom.comap_ker, ← hχψ]
    exact hχray
  have hray₂ : raySubgroup K (v.asIdeal ^ a * m) ≤
      ψ.ker.comap (Subgroup.inclusion (coprimeIdeals_mono K hvm)) := by
    rw [MonoidHom.comap_ker, ← hφψ]
    exact hray
  let J₁ : CongruenceSubgroup K := ⟨supportModulus K S (max 1 (max t₀ t₁)),
    supportModulus_ne_bot K S _, ψ.ker.comap (Subgroup.inclusion (coprimeIdeals_mono K htm)),
    hray₁⟩
  let J₂ : CongruenceSubgroup K := ⟨v.asIdeal ^ a * m, hvm0,
    ψ.ker.comap (Subgroup.inclusion (coprimeIdeals_mono K hvm)), hray₂⟩
  have h₁ : J₁.ambient = ψ.ker.map (coprimeIdeals K m).subtype ⊓
      coprimeIdeals K (supportModulus K S (max 1 (max t₀ t₁))) := hamb _ htm
  have h₂ : J₂.ambient = ψ.ker.map (coprimeIdeals K m).subtype ⊓
      coprimeIdeals K (v.asIdeal ^ a * m) := hamb _ hvm
  have hJ : CongruenceEquivalent K J₁ J₂ := by
    refine ⟨supportModulus K S (max 1 (max t₀ t₁)) * (v.asIdeal ^ a * m),
      mul_ne_zero (supportModulus_ne_bot K S _) hvm0, Ideal.mul_le_right, Ideal.mul_le_left, ?_⟩
    rw [h₁, h₂, inf_assoc, inf_assoc, inf_eq_right.mpr (coprimeIdeals_mono K Ideal.mul_le_right),
      inf_eq_right.mpr (coprimeIdeals_mono K Ideal.mul_le_left)]
  obtain ⟨G, hG, hJ₁G, -⟩ := exists_congruence_gcd K J₁ J₂ hJ
  have hvS : v.asIdeal ^ a ⊔ supportModulus K S (max 1 (max t₀ t₁)) = ⊤ := by
    apply Ideal.pow_sup_eq_top
    by_contra h
    have hle : supportModulus K S (max 1 (max t₀ t₁)) ≤ v.asIdeal :=
      le_sup_right.trans ((v.isPrime.isMaximal v.ne_bot).eq_of_le h le_sup_left).symm.le
    have hmv := (hS v).mp ((supportModulus_le_prime_iff K S _ ht0 v).mp hle)
    rw [sup_eq_left.mpr hmv] at hcop
    exact v.isPrime.ne_top hcop
  have hGm : G.modulus = m := by
    rw [hG]
    change supportModulus K S (max 1 (max t₀ t₁)) ⊔ v.asIdeal ^ a * m = m
    rw [sup_comm, Ideal.mul_sup_eq_of_coprime_left hvS, sup_eq_left.mpr htm]
  have hIeq : coprimeIdeals K m = coprimeIdeals K (supportModulus K S (max 1 (max t₀ t₁))) := by
    ext x
    rw [mem_coprimeIdeals_iff_count_eq_zero, mem_coprimeIdeals_iff_count_eq_zero]
    refine forall_congr' fun p => imp_congr_left ?_
    rw [supportModulus_le_prime_iff K S _ ht0 p, hS p]
  intro x hx
  have hxG : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ G.ambient := by
    apply G.closure_rayGenerators_le_ambient
    rw [hGm]
    exact hx
  have hxt : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      coprimeIdeals K (supportModulus K S (max 1 (max t₀ t₁))) := by
    rw [← hIeq]
    exact x.2
  have hx1 : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ J₁.ambient := by
    rw [hJ₁G]
    exact ⟨hxG, hxt⟩
  rw [h₁] at hx1
  obtain ⟨⟨z, hz, hzx⟩, -⟩ := hx1
  rw [show x = z from Subtype.ext hzx.symm]
  exact hz

include hNF_K hNF_L in
/-- The decomposition-field Artin map can be defined at m after removing the split prime. -/
theorem exists_artinMap_remove_split_prime [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hsplit : v.asIdeal ∈ splittingIdeals K L) :
    ∃ ψ : coprimeIdeals K m →* (L ≃ₐ[K] L),
      IsArtinMap K m L ψ ∧ raySubgroup K m ≤ ψ.ker ∧
      ψ.comp (Subgroup.inclusion (coprimeIdeals_mono K
        (show v.asIdeal ^ a * m ≤ m from Ideal.mul_le_left))) = φ := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hUm := isUnramifiedAway_remove_split_prime K L v m a hU hsplit
  obtain ⟨ψ, hψ, -⟩ := exists_artinMap K m L hm hUm
  exact ⟨ψ, hψ, ray_kernel_remove_split_prime K L v m hm hcop a φ hφ hray ψ hψ hUm,
    isArtinMap_unique K _ L hU (isArtinMap_comp_inclusion K L Ideal.mul_le_left ψ hψ) hφ⟩

include hvw hNF_K hNF_L in
/-- In the decomposition field, both the ray principal and the removed prime power are killed. -/
theorem rayArtin_restrict_decompositionSubfield_eq_one
    [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker)
    (u : rayElements K m) :
    AlgEquiv.restrictNormalHom (decompositionSubfield K L w)
      (rayArtinMap K L v m a φ u) = 1 := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsAbelianGalois K (decompositionSubfield K L w) := IsAbelianGalois.tower_bot K _ L
  haveI : NumberField (decompositionSubfield K L w) := NumberField.of_module_finite K _
  haveI : Module.Finite (𝓞 K) (𝓞 (decompositionSubfield K L w)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have hsplitZ := decompositionSubfield_splits K L v w
  have hφZ := isArtinMap_restrict K _ L (decompositionSubfield K L w) φ hφ
  have hUZ := isUnramifiedAway_subfield K _ L (decompositionSubfield K L w) hU
  have hrayZ : raySubgroup K (v.asIdeal ^ a * m) ≤
      ((AlgEquiv.restrictNormalHom (decompositionSubfield K L w)).comp φ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hray hx, map_one]
  obtain ⟨ψ, hψ, hψray, hψφ⟩ := exists_artinMap_remove_split_prime K (decompositionSubfield K L w)
    v m hm hcop a _ hφZ hrayZ hUZ hsplitZ
  have hUmZ := isUnramifiedAway_remove_split_prime K (decompositionSubfield K L w) v m a hUZ hsplitZ
  have hPm : primeIdealUnit K v ∈ coprimeIdeals K m :=
    Subgroup.subset_closure ⟨v.asIdeal, v.ne_bot, hcop, primeIdealUnit_coe K v⟩
  have hum : toPrincipalIdeal (𝓞 K) K (u : Kˣ) ∈ coprimeIdeals K m :=
    principal_mem_coprime_of_mem_rayElements K m u u.2
  obtain ⟨r, hr⟩ := erased_ray_principal_eq_prime_zpow K v m hcop a ha (primeIdealUnit K v)
    (primeIdealUnit_coe K v) u u.2
  have hP1 : ψ ⟨_, hPm⟩ = 1 := normImage_le_artin_ker K m _ hUmZ ψ hψ
    (mem_normImage_of_splits K m _ hsplitZ hcop ⟨_, hPm⟩ (primeIdealUnit_coe K v))
  have hu1 : ψ ⟨_, hum⟩ = 1 := by
    apply hψray
    obtain ⟨y, hy, hyu⟩ := principal_mem_ray_of_mem_rayElements K m u u.2
    rw [show (⟨_, hum⟩ : coprimeIdeals K m) = y from Subtype.ext hyu.symm]
    exact hy
  have hincl : Subgroup.inclusion (coprimeIdeals_mono K (show v.asIdeal ^ a * m ≤ m from
      Ideal.mul_le_left)) (eraseModulusFactors K (v.asIdeal ^ a * m)
        (toPrincipalIdeal (𝓞 K) K (u : Kˣ))) = ⟨_, hPm⟩ ^ r * ⟨_, hum⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion, hr]
    rfl
  have key := DFunLike.congr_fun hψφ (eraseModulusFactors K (v.asIdeal ^ a * m)
    (toPrincipalIdeal (𝓞 K) K (u : Kˣ)))
  rw [MonoidHom.comp_apply, hincl, map_mul, map_zpow, hP1, hu1, one_zpow, one_mul] at key
  rw [rayArtinMap, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact key.symm

include hvw hNF_K hNF_L in
/-- The first inclusion of Janusz V.11.2 is the fixed-field criterion applied to the restriction. -/
theorem rayArtin_range_le_stabilizer [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker) :
    (rayArtinMap K L v m a φ).range ≤
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rintro _ ⟨u, rfl⟩
  have h := rayArtin_restrict_decompositionSubfield_eq_one K L v w m hm hcop a ha φ hφ hU hray u
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker] at h
  rw [← IntermediateField.fixingSubgroup_fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)]
  exact h

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
include hvw hNF_K hNF_L in
/-- Janusz V.11.2's reverse-inclusion argument: a subgroup containing the ray image
cannot have prime relative index in the decomposition group. -/
theorem not_prime_relIndex_of_rayArtin_range_le
    [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker)
    (G₀ : Subgroup (L ≃ₐ[K] L))
    (himage : (rayArtinMap K L v m a φ).range ≤ G₀)
    (hG₀ : G₀ ≤ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ¬Nat.Prime (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) := by
  classical
  intro hprime
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : NeZero (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) := ⟨hprime.ne_zero⟩
  -- the decomposition field Z and the fixed field E of G₀
  have hZE : IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) ≤
      IntermediateField.fixedField G₀ := decompositionSubfield_le_fixedField K L w G₀ hG₀
  letI : Algebra (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (IntermediateField.fixedField G₀) := (IntermediateField.inclusion hZE).toAlgebra
  haveI : IsScalarTower (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (IntermediateField.fixedField G₀) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal))
      (IntermediateField.fixedField G₀) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdeg : Module.finrank
      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (IntermediateField.fixedField G₀) =
        G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
    finrank_fixedField_over_decompositionSubfield K L w G₀ hG₀
  haveI : IsAbelianGalois K (IntermediateField.fixedField G₀) := IsAbelianGalois.tower_bot K _ L
  haveI : IsAbelianGalois K
      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) :=
    IsAbelianGalois.tower_bot K _ L
  haveI : NumberField (IntermediateField.fixedField G₀) := NumberField.of_module_finite K _
  haveI : NumberField
      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) :=
    NumberField.of_module_finite K _
  haveI : IsAbelianGalois
      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) L :=
    IsAbelianGalois.tower_top K _ L
  haveI : IsAbelianGalois
      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (IntermediateField.fixedField G₀) :=
    IsAbelianGalois.tower_bot _ (IntermediateField.fixedField G₀) L
  -- the cyclotomic square
  letI : Algebra
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (IntermediateField.fixedField G₀)) :=
    cyclotomicBaseChangeAlgebra _ _ _
  haveI := cyclotomicBaseChange_tower
    (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
    (IntermediateField.fixedField G₀) (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
  have hgen := cyclotomicBaseChange_adjoin_eq_top
    (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
    (IntermediateField.fixedField G₀) (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
  haveI hKBF : IsScalarTower K
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (IntermediateField.fixedField G₀)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply K
        (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
          (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) x,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply
        (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
        (IntermediateField.fixedField G₀), ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K (IntermediateField.fixedField G₀)]
    rfl
  have hζ := IsCyclotomicExtension.zeta_spec (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
          (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
              (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
  haveI : IsTotallyComplex (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) :=
          NumberField.isTotallyComplex_of_algebra K _
  haveI : IsAbelianGalois (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
          (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
              (IntermediateField.fixedField G₀)) := isAbelianGalois_compositum K
                  (IntermediateField.fixedField G₀) (CyclotomicField (G₀.relIndex
                      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
                          G₀)) (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
                              w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L
                                  ≃ₐ[K] L) w.asIdeal))) hgen
  obtain ⟨S₁, hS₁⟩ := exists_primesAbove_support K (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) v
  have hm' : m.map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L
      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
          w.asIdeal))))) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm
  have hvB : ∀ v' ∈ S₁, v.asIdeal.map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))))) ≤ v'.asIdeal := by
    intro v' hv'
    haveI := (hS₁ v').mp hv'
    exact Ideal.map_le_iff_le_comap.mpr
      (Ideal.LiesOver.over (P := v'.asIdeal) (p := v.asIdeal)).le
  have hcopS₁ : ∀ v' ∈ S₁, v'.asIdeal ⊔ m.map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))))) = ⊤ := by
    intro v' hv'
    have h := congrArg (Ideal.map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex
        (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
            (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))))) hcop
    rw [Ideal.map_sup, Ideal.map_top] at h
    exact eq_top_mono (sup_le_sup_right (hvB v' hv') _) h
  obtain ⟨S₂, hdisj, hreps, hcover, -, d₀, hd₀⟩ :=
    exists_paired_complement (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
        w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
            (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) hprime.pos S₁ _ hm' hcopS₁
  have hU21 : S₂.disjUnion S₁ hdisj.symm = S₁ ∪ S₂ := by
    rw [Finset.disjUnion_eq_union, Finset.union_comm]
  have hcover' : CoversNthPrimes (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
          (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (S₂.disjUnion S₁ hdisj.symm)
              := by
    rw [hU21]
    exact hcover
  have hreps' : SupportsClassRepresentatives (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L
      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
          w.asIdeal))) (S₂.disjUnion S₁ hdisj.symm) := by
    rw [hU21]
    exact hreps
  obtain ⟨p₀, hp₀⟩ := paired_hasArtinKernel (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L
      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
          w.asIdeal))) (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) hprime.pos _ hζ
              S₂ S₁ hdisj.symm hcover' hreps'
  obtain ⟨o₀, ho₀⟩ := pairedRadicalField_splits_opposite (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) (G₀.relIndex (MulAction.stabilizer (L
              ≃ₐ[K] L) w.asIdeal)) hprime.pos _ hζ
    (S₂.disjUnion S₁ hdisj.symm) S₁
  have hC := hp₀ (max p₀ d₀) (le_max_left _ _) (max p₀ o₀) (le_max_left _ _)
  haveI := hC.finiteDimensional
  haveI : NumberField (radicalField (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
          (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (pairedRadicands
              (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                  (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
                      (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (S₂.disjUnion S₁ hdisj.symm) (supportModulus (CyclotomicField (G₀.relIndex
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
              (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) S₁ (max p₀ o₀)))) :=
    NumberField.of_module_finite (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
        w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) _
  have hφE := isArtinMap_restrict K (v.asIdeal ^ a * m) L (IntermediateField.fixedField G₀) φ hφ
  have hUE := isUnramifiedAway_subfield K _ L (IntermediateField.fixedField G₀) hU
  have hrayG₀ : ∀ u : Kˣ, u ∈ rayElements K m →
      φ (eraseModulusFactors K (v.asIdeal ^ a * m) (toPrincipalIdeal (𝓞 K) K u)) ∈ G₀ :=
    fun u hu => himage ⟨⟨u, hu⟩, rfl⟩
  have hS₁v : ∀ v' ∈ S₁, (v.asIdeal ^ a * m).map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))))) ≤ v'.asIdeal := by
    intro v' hv'
    rw [Ideal.map_mul, Ideal.map_pow]
    exact Ideal.mul_le_right.trans ((Ideal.pow_le_self ha.ne').trans (hvB v' hv'))
  have hmm' : supportModulus (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) S₂
          (max p₀ d₀) ≤ m.map (algebraMap (𝓞 K) (𝓞 (CyclotomicField (G₀.relIndex
              (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
                  (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))))) :=
    hd₀ _ (le_max_right _ _)
  have hNorm : ∀ X : coprimeIdeals (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
          (supportModulus (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
              w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
                  w.asIdeal))) S₂ (max p₀ d₀)),
      X ∈ pairedSubgroup (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
          w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
              (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (supportModulus
                  (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
                          S₂ (max p₀ d₀)) S₁ →
        ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField G₀)).comp φ)
          (eraseModulusFactors K (v.asIdeal ^ a * m) (idealUnitNorm K (CyclotomicField (G₀.relIndex
              (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
                  (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) X)) = 1 := by
    intro X hX
    have h := pairedSubgroup_erased_norm_mem K (CyclotomicField (G₀.relIndex (MulAction.stabilizer
        (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
            w.asIdeal))) L (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) G₀ hG₀ (v.asIdeal ^ a * m)
                m _ hmm' φ hφ
      hU hrayG₀ S₁ hS₁v X hX
    rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
      IntermediateField.fixingSubgroup_fixedField]
    exact h
  have hvm0 : v.asIdeal ^ a * m ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) hm
  obtain ⟨ι⟩ := exists_algHom_of_erased_norm_kernel K (IntermediateField.fixedField G₀)
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
          (IntermediateField.fixedField G₀)) (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L
              ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
                  w.asIdeal))) (radicalField (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L
                      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L
                          ≃ₐ[K] L) w.asIdeal))) (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
                              w.asIdeal)) (pairedRadicands (CyclotomicField (G₀.relIndex
                                  (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                                      (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K]
                                          L) w.asIdeal))) (G₀.relIndex (MulAction.stabilizer (L
                                              ≃ₐ[K] L) w.asIdeal)) (S₂.disjUnion S₁ hdisj.symm)
                                                  (supportModulus (CyclotomicField (G₀.relIndex
                                                      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                                                          (IntermediateField.fixedField
                                                              (MulAction.stabilizer (L ≃ₐ[K] L)
                                                                  w.asIdeal))) S₁ (max p₀ o₀))))
                                                                      (v.asIdeal ^ a * m) hvm0 _
    (supportModulus_ne_bot (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
        w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) S₂
            _) _ hφE hUE _ hC hgen hNorm
  have hsplitF : ∀ v' ∈ S₁, v'.asIdeal ∈ splittingIdeals (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) (CyclotomicField (G₀.relIndex
              (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField G₀)) :=
                  fun v' hv' =>
    splittingIdeals_of_algHom (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
        w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
            (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                (IntermediateField.fixedField G₀)) (radicalField (CyclotomicField (G₀.relIndex
                    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
                        (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) (G₀.relIndex
                            (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (pairedRadicands
                                (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
                                    w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer
                                        (L ≃ₐ[K] L) w.asIdeal))) (G₀.relIndex (MulAction.stabilizer
                                            (L ≃ₐ[K] L) w.asIdeal)) (S₂.disjUnion S₁ hdisj.symm)
                                                (supportModulus (CyclotomicField (G₀.relIndex
                                                    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                                                        (IntermediateField.fixedField
                                                            (MulAction.stabilizer (L ≃ₐ[K] L)
                                                                w.asIdeal))) S₁ (max p₀ o₀)))) ι
                                                                    (ho₀ (max p₀ o₀) (le_max_right
                                                                        _ _) v' hv')
  haveI hwZv : (w.asIdeal.under (𝓞 (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)))).LiesOver v.asIdeal :=
    ⟨by rw [Ideal.under_under]; exact hvw.over⟩
  let vZ : HeightOneSpectrum (𝓞 (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal))) :=
    ⟨w.asIdeal.under (𝓞 (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
        w.asIdeal))), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩
  have hsplitBF : ∀ P ∈ vZ.asIdeal.primesOver (𝓞 (CyclotomicField (G₀.relIndex
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))), P ∈ splittingIdeals (CyclotomicField
              (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                  (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
                      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                          (IntermediateField.fixedField G₀)) := by
    rintro P ⟨hPp, hPo⟩
    haveI := hPp
    haveI := hPo
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot vZ.ne_bot P
    have hP'S : (⟨P, hPp, hP0⟩ : HeightOneSpectrum (𝓞 (CyclotomicField (G₀.relIndex
        (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
            (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))))) ∈ S₁ := (hS₁ _).mpr ⟨by
      rw [← Ideal.under_under (B := 𝓞 (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K]
          L) w.asIdeal))), ← hPo.over]
      exact hwZv.over⟩
    exact hsplitF _ hP'S
  haveI : IsGalois (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
      (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
          (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) :=
              IsCyclotomicExtension.isGalois {(G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
                  w.asIdeal))} (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
                      w.asIdeal)) (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L)
                          w.asIdeal)) (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K]
                              L) w.asIdeal)))
  have hdvd := cyclotomic_finrank_dvd_prime_pred (IntermediateField.fixedField
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (CyclotomicField (G₀.relIndex
          (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField
              (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) (G₀.relIndex (MulAction.stabilizer (L
                  ≃ₐ[K] L) w.asIdeal)) hprime
  have hBpos : 0 < Module.finrank (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L)
      w.asIdeal)) (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
          (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))) :=
              Module.finrank_pos
  have hcopdeg : Nat.Coprime (Module.finrank (IntermediateField.fixedField (MulAction.stabilizer (L
      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField G₀)) (Module.finrank
          (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
              (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                  (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))) :=
                      by
    rw [hdeg]
    exact Nat.coprime_of_lt_prime hBpos.ne' (lt_of_le_of_lt
      (Nat.le_of_dvd (Nat.sub_pos_of_lt hprime.one_lt) hdvd) (Nat.sub_lt hprime.pos one_pos))
      hprime
  have hsplitZE := splittingIdeals_of_coprime_baseChange (IntermediateField.fixedField
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField G₀)
          (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
              (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)))
                  (CyclotomicField (G₀.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal))
                      (IntermediateField.fixedField G₀)) hcopdeg vZ hsplitBF
  have hunique : Subsingleton (vZ.asIdeal.primesOver (𝓞 L)) :=
    decompositionSubfield_unique_prime K L w
  have h1 := finrank_eq_one_of_split_unique (IntermediateField.fixedField (MulAction.stabilizer (L
      ≃ₐ[K] L) w.asIdeal)) (IntermediateField.fixedField G₀) vZ hsplitZE
    (primesOver_subsingleton_of_tower (IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K]
        L) w.asIdeal)) (IntermediateField.fixedField G₀) L vZ hunique)
  rw [hdeg] at h1
  exact hprime.one_lt.ne' h1

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
include hvw in
/-- Janusz V.11.2: erased ray-principal Artin elements generate the decomposition group. -/
theorem rayArtin_range_eq_stabilizer [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hsurj : Function.Surjective φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker) :
    ((φ.comp (eraseModulusFactors K (v.asIdeal ^ a * m))).comp
      ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype)).range =
        MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hle := rayArtin_range_le_stabilizer K L v w m hm hcop a ha φ hφ hU hray
  refine le_antisymm hle ?_
  by_contra hne
  obtain ⟨G₀, hG₀, hG₀D, hprime⟩ := exists_prime_relIndex_overgroup _ _ (lt_of_le_not_ge hle hne)
  exact not_prime_relIndex_of_rayArtin_range_le K L v w m hm hcop a ha φ hφ hU hray G₀ hG₀
    hG₀D.le hprime

end Cox.ClassFieldTheory
