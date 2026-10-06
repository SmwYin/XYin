/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitFiltration
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitInvariants
import XYin.PhD.Cox.Theorem11_1.ClassFieldDiagonalHerbrand

/-! # Assembly of Janusz V.3.6–3.12 local norm indices

The unit quotient is computed separately. The full field norm index follows
the source valuation exact sequence, Herbrand multiplicativity and Hilbert90.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
attribute [local instance] localAlgebra localFinite

/-- Norms of embedded base integral units are their local-degree powers. -/
theorem unit_degree_powers_le_unitNormGroup :
    (localFieldUnitFiltration K v 0).map
      (powMonoidHom (Module.finrank (v.adicCompletion K) (w.adicCompletion L))) ≤
        unitNormGroup K L v w := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L) u,
    (fieldUnitEmbedding_mem_units_iff K L v w u).mpr hu, ?_⟩
  apply Units.ext
  change Algebra.norm (v.adicCompletion K)
    (algebraMap (v.adicCompletion K) (w.adicCompletion L) (u : v.adicCompletion K)) =
      ((u ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K)
  rw [Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]

/-- Janusz V.3.12: the actual normalized valuation, as an intertwiner to the trivial
integer line. -/
def localValuationIntertwining :
    (Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (w.adicCompletion L)ˣ).IntertwiningMap
        (Representation.trivial ℤ
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) ℤ) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (MonoidHom.toAdditiveLeft (localUnitValuation L w)).toIntLinearMap (by
      intro σ x
      change (localUnitValuation L w
        (Units.map σ.toRingHom.toMonoidHom x.toMul)).toAdd =
          (localUnitValuation L w x.toMul).toAdd
      exact congrArg Multiplicative.toAdd (localUnitValuation_aut K L v w σ x.toMul))

/-- The normalized valuation is surjective onto the integer line. -/
theorem localValuationIntertwining_surjective :
    Function.Surjective (localValuationIntertwining K L v w) := by
  intro z
  obtain ⟨x, hx⟩ := localUnitValuation_surjective L w (Multiplicative.ofAdd z)
  exact ⟨Additive.ofMul x, congrArg Multiplicative.toAdd hx⟩

/-- The valuation-zero units are exactly the kernel of the valuation intertwiner. -/
theorem localValuationSequence_exact :
    LinearMap.range (submoduleIntertwining
      (Representation.ofMulDistribMulAction
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletion L)ˣ)
      (unitSubmodule L w) (unitSubmodule_stable K L v w)).toLinearMap =
        LinearMap.ker (localValuationIntertwining K L v w).toLinearMap := by
  change LinearMap.range (unitSubmodule L w).subtype = _
  rw [Submodule.range_subtype]
  ext x
  change x.toMul ∈ localFieldUnitFiltration L w 0 ↔
    (localUnitValuation L w x.toMul).toAdd = 0
  rw [localFieldUnitFiltration_zero_eq_ker]
  rfl

variable [hLocalGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L)]
include hLocalGalois

/-- The two cyclic local-unit cohomology computations give unit norm index e. -/
theorem unit_norm_index [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)] :
    (unitNormGroup K L v w).relIndex (localFieldUnitFiltration K v 0) =
      Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator
    (α := w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
  have hfin := unit_finiteHerbrand K L v w σ hσ
  haveI := hfin.1
  haveI := hfin.2
  have hq := unit_herbrandQuotient K L v w σ hσ
  have h0 : 0 < Nat.card (tateZero (unitRepresentation K L v w) σ) := Nat.card_pos
  rw [herbrandQuotient, div_eq_one_iff_eq (by exact_mod_cast h0.ne')] at hq
  have h1 : Nat.card (tateOne (unitRepresentation K L v w) σ) =
      Nat.card (tateZero (unitRepresentation K L v w) σ) := by exact_mod_cast hq
  rw [unit_tateOne_card K L v w σ hσ] at h1
  obtain ⟨e⟩ := unit_tateZero_equiv_normQuotient K L v w σ hσ
  rw [Subgroup.relIndex, Subgroup.index, h1]
  exact (Nat.card_congr e.toEquiv).symm

omit hLocalGalois in
/-- Deep base principal units are local unit norms, by taking degree-th roots. -/
theorem deep_units_le_unitNormGroup :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, localFieldUnitFiltration K v t ≤ unitNormGroup K L v w := by
  have hd : 0 < Module.finrank (v.adicCompletion K) (w.adicCompletion L) := Module.finrank_pos
  obtain ⟨t₀, ht₀⟩ := deep_units_are_powers K v _ hd
  refine ⟨t₀, fun t ht => ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨r, hr⟩ := ht₀ t ht hz
  apply unit_degree_powers_le_unitNormGroup K L v w
  refine ⟨Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom r, ⟨r, ?_, rfl⟩, ?_⟩
  · rw [localUnitFiltration_zero]
    exact Subgroup.mem_top r
  · rw [← hr]
    exact (map_pow (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) r _).symm

/-- Janusz V.3.12: valuation exactness and Hilbert90 give the local field norm index. -/
theorem norm_index [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)] :
    (localNormGroup K L v w).index =
      Ideal.ramificationIdx v.asIdeal w.asIdeal * Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  classical
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator
    (α := w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
  let ρ := unitRepresentation K L v w
  let τ := Representation.ofMulDistribMulAction
    (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ
  let υ := Representation.trivial ℤ (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) ℤ
  let f : ρ.IntertwiningMap τ := submoduleIntertwining τ
    (unitSubmodule L w) (unitSubmodule_stable K L v w)
  let h : τ.IntertwiningMap υ := localValuationIntertwining K L v w
  have hf : Function.Injective f := submoduleIntertwining_injective τ _ _
  have hh : Function.Surjective h := localValuationIntertwining_surjective K L v w
  have he : LinearMap.range f.toLinearMap = LinearMap.ker h.toLinearMap :=
    localValuationSequence_exact K L v w
  have hA : FiniteHerbrand ρ σ := unit_finiteHerbrand K L v w σ hσ
  have hC : FiniteHerbrand υ σ := finiteHerbrand_of_moduleFinite υ σ hσ
  have hB : FiniteHerbrand τ σ :=
    finiteHerbrand_of_first_last ρ τ υ σ f h hf hh he hA hC
  have hq := herbrandQuotient_mul ρ σ τ υ f h hf hh he hσ hA hB hC
  have hqU : herbrandQuotient ρ σ = 1 := unit_herbrandQuotient K L v w σ hσ
  have hqZ : herbrandQuotient υ σ =
      (Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) : ℚ)⁻¹ :=
    herbrandQuotient_trivial_int (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) σ hσ
  rw [hqU, hqZ, one_mul] at hq
  letI : Subsingleton (tateOne τ σ) :=
    fieldUnits_tateOne_subsingleton (v.adicCompletion K) (w.adicCompletion L) σ hσ
  have hcard : Nat.card (tateZero τ σ) =
      Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
    have h1 : Nat.card (tateOne τ σ) = 1 := Nat.card_unique
    change (Nat.card (tateOne τ σ) : ℚ) / Nat.card (tateZero τ σ) = _ at hq
    rw [h1, Nat.cast_one, one_div] at hq
    exact_mod_cast inv_injective hq
  have hquot := Nat.card_congr
    (fieldUnitsTateEquiv (v.adicCompletion K) (w.adicCompletion L) σ hσ).toEquiv
  change Nat.card (tateZero τ σ) =
    Nat.card ((v.adicCompletion K)ˣ ⧸ localNormGroup K L v w) at hquot
  change Nat.card ((v.adicCompletion K)ˣ ⧸ localNormGroup K L v w) = _
  rw [← hquot, hcard, IsGalois.card_aut_eq_finrank]
  exact completion_finrank_eq_ramification_mul_inertia K L v w

end Cox.ClassFieldTheory.LocalCyclic
