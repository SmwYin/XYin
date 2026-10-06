/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitDiagonal
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-! # Finite index of the normalized unit family

The existing maximal-rank theorem supplies the source's logarithmic lattice and
finite-kernel argument. The adapters preserve the actual integer-unit values,
mathlib's distinguished deleted place, and the principal-kernel subgroup index.
The subsequent Herbrand calculation remains separate.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

/-- The actual principal-ideal kernel is equivalent to integer-ring units, preserving values. -/
theorem exists_principalUnitEquiv (L : Type*) [Field L] [NumberField L] :
    ∃ e : (toPrincipalIdeal (𝓞 L) L).ker ≃* (𝓞 L)ˣ,
      ∀ u, Units.map (algebraMap (𝓞 L) L).toMonoidHom (e u) = (u : Lˣ) := by
  let f : (𝓞 L)ˣ →* (toPrincipalIdeal (𝓞 L) L).ker :=
    (Units.map (algebraMap (𝓞 L) L).toMonoidHom).codRestrict _
      (fun x => (principalIdeal_eq_one_iff L _).mpr ⟨x, rfl⟩)
  have hinj : Function.Injective f := by
    intro x y h
    have h' := congrArg (fun z : (toPrincipalIdeal (𝓞 L) L).ker => (z : Lˣ)) h
    exact Units.map_injective (f := (algebraMap (𝓞 L) L).toMonoidHom)
      (IsFractionRing.injective (𝓞 L) L) h'
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx⟩ := (principalIdeal_eq_one_iff L a).mp ha
    exact ⟨x, Subtype.ext hx⟩
  let e' := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e'.symm, fun u => ?_⟩
  exact congrArg (fun z : (toPrincipalIdeal (𝓞 L) L).ker => (z : Lˣ)) (e'.apply_symm_apply u)

/-- A zero-sum vector is zero when every coordinate except one is zero. -/
theorem eq_zero_of_sum_eq_zero_of_restrict_eq_zero {ι A : Type*} [Fintype ι]
    [AddCommMonoid A] (i₀ : ι) (x : ι → A) (hx : ∑ i, x i = 0)
    (hrest : ∀ i, i ≠ i₀ → x i = 0) : x = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hx
  have hrest' : ∑ i : {i : ι // i ≠ i₀}, x i.val = 0 :=
    Finset.sum_eq_zero fun i _ => hrest i.val i.2
  rw [hrest', add_zero] at hx
  funext i
  by_cases hi : i = i₀
  · rw [hi, hx]
    rfl
  · exact hrest i hi

/-- Deleting one coordinate preserves independence for vectors whose coordinate sums vanish. -/
theorem linearIndependent_restrict_of_sum_eq_zero {R ι J : Type*} [Ring R] [Fintype ι]
    (i₀ : ι) (v : J → ι → R) (hsum : ∀ j, ∑ i, v j i = 0)
    (hv : LinearIndependent R v) :
    LinearIndependent R (fun j => fun i : {i : ι // i ≠ i₀} => v j i.val) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg j hj
  apply hv s g _ j hj
  apply eq_zero_of_sum_eq_zero_of_restrict_eq_zero i₀
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.mul_sum, hsum, mul_zero]
  · intro i hi
    have h := congrFun hg ⟨i, hi⟩
    simpa [Finset.sum_apply, Pi.smul_apply] using h

/-- The actual deleted unit family has maximal rank in mathlib's logarithmic space. -/
theorem principalUnitFamily_isMaxRank (L : Type*) [Field L] [NumberField L]
    (e : (toPrincipalIdeal (𝓞 L) L).ker ≃* (𝓞 L)ˣ)
    (he : ∀ u, Units.map (algebraMap (𝓞 L) L).toMonoidHom (e u) = (u : Lˣ))
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hLI : LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ Units.dirichletUnitTheorem.w₀} =>
        fun v : InfinitePlace L => (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L)))) :
    Units.IsMaxRank (fun i : Fin (Units.rank L) => e (u ((Units.equivFinRank L i).val))) := by
  have hsum : ∀ j : {w : InfinitePlace L // w ≠ Units.dirichletUnitTheorem.w₀},
      ∑ v, (fun v : InfinitePlace L => (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L))) v = 0 :=
    fun j => principalUnit_sum_weightedLog L (u j.val)
  have h1 := linearIndependent_restrict_of_sum_eq_zero Units.dirichletUnitTheorem.w₀ _ hsum hLI
  have h2 := h1.comp (Units.equivFinRank L) (Units.equivFinRank L).injective
  convert h2 using 1
  funext i w
  rw [Function.comp_apply, Units.dirichletUnitTheorem.logEmbedding_component]
  beta_reduce
  have h3 : algebraMap (𝓞 L) L ((e (u (Units.equivFinRank L i).val) : 𝓞 L)) =
      ((u (Units.equivFinRank L i).val : Lˣ) : L) := congrArg Units.val (he _)
  rw [h3]

/-- A finite-index generated subfamily implies finite index for the full family across
an equivalence. -/
theorem finiteIndex_closure_of_equiv_subfamily {G H ι κ : Type*} [Group G] [Group H]
    (e : G ≃* H) (u : ι → G) (r : κ → ι)
    (h : (Subgroup.closure (Set.range (fun i => e (u (r i))))).FiniteIndex) :
    (Subgroup.closure (Set.range u)).FiniteIndex := by
  have hle : Subgroup.closure (Set.range (fun i => e (u (r i)))) ≤
      (Subgroup.closure (Set.range u)).map (e : G →* H) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨u (r k), ⟨r k, rfl⟩, rfl⟩
  have h2 : ((Subgroup.closure (Set.range u)).map (e : G →* H)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  rw [Subgroup.finiteIndex_iff] at h2 ⊢
  rwa [Subgroup.index_map_equiv] at h2

/-- Full weighted-log independence gives finite index in the actual principal-unit kernel. -/
theorem principalUnitFamily_closure_finiteIndex (L : Type*) [Field L] [NumberField L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hLI : LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ Units.dirichletUnitTheorem.w₀} =>
        fun v : InfinitePlace L => (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L)))) :
    (Subgroup.closure (Set.range u)).FiniteIndex := by
  obtain ⟨e, he⟩ := exists_principalUnitEquiv L
  have hmax := principalUnitFamily_isMaxRank L e he u hLI
  have hfin := Units.isMaxRank_iff_closure_finiteIndex.mp hmax
  exact finiteIndex_closure_of_equiv_subfamily e u (fun i => (Units.equivFinRank L i).val) hfin

/-- Janusz V.2.3: one equivariant family has the diagonal relation and generates a subgroup
of finite index in the actual global-unit kernel. -/
theorem exists_equivariant_unit_lattice (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [hGalois : IsGalois K L] :
    ∃ w : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker,
      (∀ (σ : L ≃ₐ[K] L) v, σ • (w v : Lˣ) = (w (σ • v) : Lˣ)) ∧
      (∀ a : InfinitePlace L → ℤ,
        (∏ v, w v ^ a v) = 1 ↔ ∃ n : ℤ, ∀ v, a v = n) ∧
      (Subgroup.closure (Set.range w)).FiniteIndex := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨u, hequiv, hprod, hLI⟩ := exists_normalized_equivariant_unit_family K L
  exact ⟨u, hequiv,
    fun a => unitRelation_iff_constant L u _ hprod (hLI Units.dirichletUnitTheorem.w₀) a,
    principalUnitFamily_closure_finiteIndex L u (hLI _)⟩

end Cox.ClassFieldTheory
