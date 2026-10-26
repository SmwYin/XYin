/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionEmbedding
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionResidue
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompleteDVR
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Degree, ramification and residue fields of completions

Janusz II.3.3–3.8 and III.1.1. The integral-closure argument precedes the
fundamental identity, so the local degree is not deduced from an assumed local Galois group.
-/

open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Janusz II.2.4: powers of the completed maximal ideal give its valuation topology. -/
theorem completionIntegers_isAdic (v : HeightOneSpectrum (𝓞 K)) :
    IsAdic (maximalIdeal (v.adicCompletionIntegers K)) := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  have hpow : ∀ n : ℕ, Valued.v ((π : v.adicCompletion K) ^ n) = WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · have hset : ((maximalIdeal (v.adicCompletionIntegers K) ^ n : Ideal _) :
        Set (v.adicCompletionIntegers K)) = Subtype.val ⁻¹'
          {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-(n : ℤ))} := by
      ext a
      exact completed_mem_maximalIdeal_pow_iff K v a n
    rw [hset]
    refine IsOpen.preimage continuous_subtype_val ?_
    have hr : Valued.v.restrict ((π : v.adicCompletion K) ^ n) ≠ 0 := by
      rw [Ne, Valuation.restrict_eq_zero_iff, hpow]
      exact WithZero.exp_ne_zero
    convert Valued.isOpen_closedBall (v.adicCompletion K) hr using 1
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.restrict_le_iff, hpow]
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_induced Subtype.val _ _).mp hs
    have hu' : u ∈ nhds (0 : v.adicCompletion K) := hu
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu'
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ).ne'
    refine ⟨n, fun a ha => hus (hγ ?_)⟩
    have ha' := (completed_mem_maximalIdeal_pow_iff K v a n).mp ha
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt ha' hn

/-- Janusz II.2.2: the closed valuation ring in a complete field is complete. -/
theorem completionIntegers_completeSpace (v : HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (v.adicCompletionIntegers K) := by
  exact (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

/-- Janusz II.2.2–2.4: the completed valuation ring is adically complete. -/
theorem completionIntegers_adicComplete (v : HeightOneSpectrum (𝓞 K)) :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
  haveI := completionIntegers_completeSpace K v
  exact ((completionIntegers_isAdic K v).isAdicComplete_iff).mpr ⟨inferInstance, inferInstance⟩

/-- Janusz II.2.7: completion preserves the residue field with its actual quotient map. -/
theorem exists_completionResidueEquiv (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : ((𝓞 K) ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K),
      ∀ a : 𝓞 K, e (Ideal.Quotient.mk v.asIdeal a) =
        residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  let f : 𝓞 K →+* ResidueField (v.adicCompletionIntegers K) :=
    (residue _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  have hmem : ∀ x : v.adicCompletionIntegers K,
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ 1) x = 0 ↔
        residue _ x = 0 := by
    intro x
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, residue_eq_zero_iff]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := completedPrimaryResidueMap_surjective K v 1 (Ideal.Quotient.mk _ x)
    refine ⟨a, ?_⟩
    rw [completedPrimaryResidueMap_apply, ← sub_eq_zero, ← map_sub, hmem] at ha
    change residue _ (algebraMap _ _ a) = residue _ x
    rwa [← sub_eq_zero, ← map_sub]
  have hker : RingHom.ker f = v.asIdeal := by
    rw [← pow_one v.asIdeal, ← completedPrimaryResidueMap_ker K v 1]
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, completedPrimaryResidueMap_apply, hmem]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj),
    fun a => rfl⟩

/-- The residue equivalence induced by the fixed global integer embedding. -/
def completionResidueEquiv (v : HeightOneSpectrum (𝓞 K)) :
    ((𝓞 K) ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K) :=
  Classical.choose (exists_completionResidueEquiv K v)

/-- The chosen residue equivalence agrees with reduction of global integers. -/
theorem completionResidueEquiv_apply (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    completionResidueEquiv K v (Ideal.Quotient.mk v.asIdeal a) =
      residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  exact Classical.choose_spec (exists_completionResidueEquiv K v) a

/-- A completed valuation ring of a number field is a proper valuation subring. -/
theorem adicCompletionIntegers_ne_top (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletionIntegers K ≠ ⊤ := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  intro htop
  have hmem : (π : v.adicCompletion K)⁻¹ ∈ (⊤ : ValuationSubring (v.adicCompletion K)) :=
    ValuationSubring.mem_top _
  rw [← htop, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hπ, ← WithZero.exp_neg,
    neg_neg] at hmem
  exact absurd hmem (not_le.mpr (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num))

section Extension
variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hvw

/-- Janusz II.3.8(a–c): the normalized valuations extend with the global ramification index. -/
theorem completion_valuation_map (x : v.adicCompletion K) :
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) (completionEmbedding K L v w x) =
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x ^
        Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  open WithZeroTopology in
  have hcontL : Continuous (Valued.v : w.adicCompletion L → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective L w)
  open WithZeroTopology in
  have hcontK : Continuous (Valued.v : v.adicCompletion K → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v)
  have hdense : DenseRange (FinitePlace.embedding v) :=
    UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  open WithZeroTopology in
  have heq := hdense.equalizer (hcontL.comp (completionEmbedding_continuous K L v w))
    (hcontK.pow (Ideal.ramificationIdx v.asIdeal w.asIdeal)) (funext fun y => ?_)
  · exact congrFun heq x
  · simp only [Function.comp_apply]
    rw [completionEmbedding_commutes]
    change Valued.v ((algebraMap K L y : L) : w.adicCompletion L) =
      Valued.v ((y : K) : v.adicCompletion K) ^ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
    exact (HeightOneSpectrum.valuation_liesOver L v w y).symm

attribute [local instance] completionAlgebra completion_finiteDimensional

/-- The two normalized completed valuations define the same order on the base field. -/
theorem completion_valuation_hasExtension :
    Valuation.HasExtension
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) := by
  have he : Ideal.ramificationIdx v.asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot
  refine ⟨fun r s => ?_⟩
  change Valued.v r ≤ Valued.v s ↔
    Valued.v (completionEmbedding K L v w r) ≤ Valued.v (completionEmbedding K L v w s)
  rw [completion_valuation_map, completion_valuation_map]
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' he).symm

/-- The compatible action of base local integers on the upstairs completed field. -/
@[reducible]
def completionIntegerFieldAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  ((completionEmbedding K L v w).comp (v.adicCompletionIntegers K).subtype).toAlgebra

attribute [local instance] completionIntegerFieldAlgebra

/-- The completed field embedding restricts to the actual local integer rings. -/
@[reducible]
def completionIntegerAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  letI := completion_valuation_hasExtension K L v w
  Valuation.HasExtension.instAlgebra_valuationSubring
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)

attribute [local instance] completionIntegerAlgebra

/-- Compatibility of the integer embedding with the fixed completed field embedding. -/
theorem completion_integerEmbedding_coe (a : v.adicCompletionIntegers K) :
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) a :
      w.adicCompletion L) = completionEmbedding K L v w a := by
  rfl

/-- The base local integer action factors through its fraction field. -/
theorem completion_integerField_isScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The same local integer action factors through the upstairs local integers. -/
theorem completion_integerRing_isScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) := by
  exact IsScalarTower.of_algebraMap_eq fun a => (completion_integerEmbedding_coe K L v w a).symm

attribute [local instance] completion_integerField_isScalarTower
  completion_integerRing_isScalarTower

/-- The restriction of the completion embedding is a local ring homomorphism. -/
theorem completion_integer_isLocalHom :
    IsLocalHom (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
  letI := completion_valuation_hasExtension K L v w
  exact Valuation.HasExtension.instIsLocalHomValuationInteger

attribute [local instance] completion_integer_isLocalHom

/-- The completed extension is separable, since the completed base field has
characteristic zero. -/
theorem completion_isSeparable :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (w.adicCompletion L) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- Janusz II.3.3: the chosen upstairs valuation ring is the integral closure. -/
theorem completion_integers_isIntegralClosure :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) := by
  haveI := completionIntegers_adicComplete K v
  haveI := completion_isSeparable K L v w
  exact complete_valuationSubring_isIntegralClosure (v.adicCompletionIntegers K)
    (v.adicCompletion K) (w.adicCompletion L) (w.adicCompletionIntegers L)
    (adicCompletionIntegers_ne_top L w)

/-- Janusz II.3.3: the extension of completed integer rings is finite. -/
theorem completion_integers_finite :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  haveI := completionIntegers_adicComplete K v
  haveI := completion_isSeparable K L v w
  exact complete_valuationSubring_finite (v.adicCompletionIntegers K)
    (v.adicCompletion K) (w.adicCompletion L) (w.adicCompletionIntegers L)
    (adicCompletionIntegers_ne_top L w)

attribute [local instance] completion_integers_finite

/-- The completed maximal ideals lie over one another for the fixed integer embedding. -/
theorem completion_maximal_liesOver :
    (maximalIdeal (w.adicCompletionIntegers L)).LiesOver
      (maximalIdeal (v.adicCompletionIntegers K)) := by
  exact inferInstance

attribute [local instance] completion_maximal_liesOver

/-- Janusz II.3.8(b): completion preserves the maximal-ideal power factorization. -/
theorem completion_map_maximal_eq_pow :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
      (maximalIdeal (v.adicCompletionIntegers K)) =
        maximalIdeal (w.adicCompletionIntegers L) ^
          Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  rw [completed_maximalIdeal_eq_span K v π hπ, Ideal.map_span, Set.image_singleton]
  ext x
  rw [completed_mem_span_iff L w, completed_mem_maximalIdeal_pow_iff L w,
    completion_integerEmbedding_coe, completion_valuation_map, hπ, ← WithZero.exp_nsmul]
  simp

/-- Janusz II.3.8(c): completion preserves the ramification index. -/
theorem completion_ramificationIdx_eq :
    Ideal.ramificationIdx (maximalIdeal (v.adicCompletionIntegers K))
      (maximalIdeal (w.adicCompletionIntegers L)) =
        Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  refine Ideal.ramificationIdx_spec (completion_map_maximal_eq_pow K L v w).le ?_
  rw [completion_map_maximal_eq_pow K L v w]
  intro hle
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer L w
  have hπm : π ∈ maximalIdeal (w.adicCompletionIntegers L) := by
    rw [completed_maximalIdeal_eq_span L w π hπ]
    exact Ideal.mem_span_singleton_self π
  have h2 := (completed_mem_maximalIdeal_pow_iff L w _ _).mp
    (hle (Ideal.pow_mem_pow hπm (Ideal.ramificationIdx v.asIdeal w.asIdeal)))
  rw [SubmonoidClass.coe_pow, map_pow, hπ, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at h2
  simp at h2

/-- Janusz II.3.8(d): both residue equivalences commute with the base inclusion. -/
theorem completion_residueEquiv_natural (a : (𝓞 K) ⧸ v.asIdeal) :
    completionResidueEquiv L w (algebraMap ((𝓞 K) ⧸ v.asIdeal) ((𝓞 L) ⧸ w.asIdeal) a) =
      algebraMap (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)) (completionResidueEquiv K v a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, completionResidueEquiv_apply,
    completionResidueEquiv_apply, IsLocalRing.ResidueField.algebraMap_residue]
  congr 1
  apply Subtype.ext
  rw [completion_integerEmbedding_coe, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  change FinitePlace.embedding w (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x)) =
    completionEmbedding K L v w (FinitePlace.embedding v (algebraMap (𝓞 K) K x))
  rw [completionEmbedding_commutes, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- Janusz II.3.8(d): completion preserves the residue degree. -/
theorem completion_inertiaDeg_eq :
    Ideal.inertiaDeg (maximalIdeal (v.adicCompletionIntegers K))
      (maximalIdeal (w.adicCompletionIntegers L)) =
        Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  rw [Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap]
  symm
  exact Algebra.finrank_eq_of_equiv_equiv (completionResidueEquiv K v)
    (completionResidueEquiv L w)
    (RingHom.ext fun a => (completion_residueEquiv_natural K L v w a).symm)

/-- Janusz II.3.8(e): the local fundamental identity is `[L_w:K_v]=e(w/v)f(w/v)`. -/
theorem completion_finrank_eq_ramification_mul_inertia :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Ideal.ramificationIdx v.asIdeal w.asIdeal * Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  rw [← completion_ramificationIdx_eq, ← completion_inertiaDeg_eq]
  exact (Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := w.adicCompletionIntegers L)
    (K := v.adicCompletion K) (L := w.adicCompletion L)
    (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K))).symm

/-- The local degree is the order of the decomposition subgroup. -/
theorem completion_finrank_eq_card_stabilizer [IsGalois K L] :
    letI := completionAlgebra K L v w
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
  show Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
  rw [completion_finrank_eq_ramification_mul_inertia]
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Algebra.IsSeparable (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) := by
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
    haveI : Algebra.IsAlgebraic (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal v.ne_bot w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L)]


end Extension
end Cox.ClassFieldTheory
