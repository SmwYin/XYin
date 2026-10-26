/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionDegree
import XYin.PhD.Cox.Theorem11_1.ClassFieldValuationTransport
import Mathlib.Topology.Algebra.UniformRing

/-! # Decomposition groups and local automorphisms

Janusz III.1.1, p.95: valuation preservation, extension by completion, and degree comparison.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

/-- Fix the completion algebra constructed before reciprocity. -/
@[reducible]
def localAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  completionAlgebra K L v w

attribute [local instance] localAlgebra

/-- The fixed completion extension is finite-dimensional. -/
@[reducible]
def localFinite : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
  completion_finiteDimensional K L v w

attribute [local instance] localFinite

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Janusz III.1.1: fraction decomposition extends valuation invariance to the field. -/
theorem stabilizer_valuation
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : L) :
    w.valuation L ((σ : L ≃ₐ[K] L) x) = w.valuation L x := by
  have hσ : Ideal.map (RingOfIntegers.mapRingEquiv
      (σ : L ≃ₐ[K] L).toRingEquiv).toRingHom w.asIdeal = w.asIdeal := by
    have h : (σ : L ≃ₐ[K] L) • w.asIdeal = w.asIdeal := MulAction.mem_stabilizer_iff.mp σ.2
    rw [Ideal.pointwise_smul_def] at h
    convert h using 2
  exact primeTransport_valuation L (σ : L ≃ₐ[K] L).toRingEquiv w w hσ x

/-- Janusz III.1.1: the stabilizer acts continuously on the valued global field. -/
theorem stabilizer_withVal_continuous
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    Continuous (WithVal.congr (w.valuation L) (w.valuation L)
      (σ : L ≃ₐ[K] L).toRingEquiv) := by
  set f := WithVal.congr (w.valuation L) (w.valuation L) (σ : L ≃ₐ[K] L).toRingEquiv with hf
  have hv : ∀ y : WithVal (w.valuation L), Valued.v (f y) = Valued.v y := by
    intro y
    rw [hf, WithVal.congr_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
    exact stabilizer_valuation (K := K) (L := L) (w := w) σ y.ofVal
  refine (uniformContinuous_of_continuousAt_zero f ?_).continuous
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  refine ⟨γ, trivial, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hy ⊢
  rwa [hv]

/-- Janusz II.2.2 and III.1.1: a stabilizer element extends to a continuous local automorphism. -/
theorem exists_completion_stabilizerAut
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ τ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      Continuous τ ∧ ∀ x : L,
        τ (FinitePlace.embedding w x) = FinitePlace.embedding w ((σ : L ≃ₐ[K] L) x) := by
  have hc := stabilizer_withVal_continuous (K := K) (L := L) (w := w) σ
  have hc' := stabilizer_withVal_continuous (K := K) (L := L) (w := w) σ⁻¹
  let f := WithVal.congr (w.valuation L) (w.valuation L) (σ : L ≃ₐ[K] L).toRingEquiv
  let τ₀ : w.adicCompletion L ≃+* w.adicCompletion L :=
    UniformSpace.Completion.mapRingEquiv f hc hc'
  have hτ₀ : ∀ x : L, τ₀ (FinitePlace.embedding w x) =
      FinitePlace.embedding w ((σ : L ≃ₐ[K] L) x) := fun x =>
    UniformSpace.Completion.mapRingHom_coe (f := f.toRingHom) hc _
  have hτc : Continuous τ₀ := UniformSpace.Completion.continuous_map
  have hdense : DenseRange (FinitePlace.embedding v) :=
    UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have hcomm : ∀ c : v.adicCompletion K,
      τ₀ (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) c := by
    intro c
    have heq := hdense.equalizer (hτc.comp (completionEmbedding_continuous K L v w))
      (completionEmbedding_continuous K L v w) (funext fun k => ?_)
    · exact congrFun heq c
    · simp only [Function.comp_apply]
      rw [completionEmbedding_commutes, hτ₀, AlgEquiv.commutes]
  exact ⟨AlgEquiv.ofRingEquiv hcomm, hτc, hτ₀⟩

/-- Janusz III.1 after Lemma 1.1: each prime-stabilizing global automorphism extends
uniquely to the completion, giving a faithful homomorphism. -/
theorem exists_completion_stabilizerMap :
    ∃ ι : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →*
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L),
      Function.Injective ι ∧ ∀ σ x,
        ι σ (FinitePlace.embedding w x) = FinitePlace.embedding w ((σ : L ≃ₐ[K] L) x) := by
  choose τ hτc hτ using exists_completion_stabilizerAut K L v w
  have hdense : DenseRange (FinitePlace.embedding w) :=
    UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (w.valuation L)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have hext : ∀ α β : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      Continuous α → Continuous β →
        (∀ x, α (FinitePlace.embedding w x) = β (FinitePlace.embedding w x)) → α = β :=
    fun α β hα hβ h => AlgEquiv.ext (congrFun (hdense.equalizer hα hβ (funext h)))
  refine ⟨{ toFun := τ, map_one' := ?_, map_mul' := ?_ }, ?_, hτ⟩
  · refine hext _ _ (hτc 1) continuous_id fun x => ?_
    rw [hτ]
    rfl
  · intro σ σ'
    refine hext _ _ (hτc (σ * σ')) ((hτc σ).comp (hτc σ')) fun x => ?_
    rw [hτ, AlgEquiv.mul_apply, hτ, hτ]
    rfl
  · intro σ σ' h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have h1 := hτ σ x
    rw [show τ σ = τ σ' from h, hτ σ' x] at h1
    exact (FinitePlace.embedding w).injective h1.symm

/-- The completion at a chosen prime of a global Galois extension is Galois. -/
theorem completion_isGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨ι, hι, -⟩ := exists_completion_stabilizerMap K L v w
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
    completion_finrank_eq_card_stabilizer K L v w
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [hfin]
    exact Nat.card_le_card_of_injective ι hι

/-- The local automorphisms are exactly the global decomposition subgroup. -/
theorem completion_aut_equiv_stabilizer :
    Nonempty ((w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) ≃*
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
  obtain ⟨ι, hι, -⟩ := exists_completion_stabilizerMap K L v w
  haveI := completion_isGalois K L v w
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
    completion_finrank_eq_card_stabilizer K L v w
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) =
      Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  have hbij : Function.Bijective ι := (Nat.bijective_iff_injective_and_card ι).mpr ⟨hι, hcard⟩
  exact ⟨(MulEquiv.ofBijective ι hbij).symm⟩

/-- Cyclicity passes to the decomposition subgroup and hence to the completed extension. -/
theorem completion_aut_isCyclic [IsCyclic (L ≃ₐ[K] L)] :
    IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
  obtain ⟨e⟩ := completion_aut_equiv_stabilizer K L v w
  exact isCyclic_of_injective e.toMonoidHom e.injective

end Cox.ClassFieldTheory.LocalCyclic
