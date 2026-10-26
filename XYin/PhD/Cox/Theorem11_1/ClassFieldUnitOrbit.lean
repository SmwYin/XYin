/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitAveraging

/-! # The orbitwise unit family in Janusz V.2.3

The supplied section of restriction on infinite places need not be equivariant.
The source stabilizer condition makes the actual transported unit independent of
its transporter. This is the intermediate small family, before logarithmic rank,
relation normalization or finite-index conclusions are imposed.
-/

noncomputable section
namespace Cox.GroupAction

/-- Two transporters have the same value whenever the source stabilizer fixes that value. -/
theorem smul_eq_of_stabilizer_fixed {G X Y : Type*} [Group G] [MulAction G X]
    [MulAction G Y] {x : X} {y : Y}
    (hy : ∀ γ : G, γ • x = x → γ • y = y) {g h : G}
    (hgh : g • x = h • x) : g • y = h • y := by
  have h1 : (h⁻¹ * g) • x = x := by rw [mul_smul, hgh, inv_smul_smul]
  have h2 := hy _ h1
  rw [mul_smul, inv_smul_eq_iff] at h2
  exact h2

end Cox.GroupAction

namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

section Family
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable (r : InfinitePlace K → InfinitePlace L)
  (hr : ∀ v, (r v).comap (algebraMap K L) = v)
  (u : InfinitePlace K → Lˣ)

/-- Transport the supplied unit by an actual automorphism carrying the chosen lift to the place. -/
def orbitUnitFamily (w : InfinitePlace L) : Lˣ :=
  (InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
    (hr (w.comap (algebraMap K L)))).choose • u (w.comap (algebraMap K L))

/-- Stabilizer fixedness makes the chosen family agree with every valid transporter. -/
theorem orbitUnitFamily_eq_smul
    (hu : ∀ v (σ : L ≃ₐ[K] L), σ • r v = r v → σ • u v = u v)
    (w : InfinitePlace L) (σ : L ≃ₐ[K] L)
    (hσ : σ • r (w.comap (algebraMap K L)) = w) :
    orbitUnitFamily K L r hr u w = σ • u (w.comap (algebraMap K L)) := by
  unfold orbitUnitFamily
  exact GroupAction.smul_eq_of_stabilizer_fixed (hu _)
    ((InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
      (hr (w.comap (algebraMap K L)))).choose_spec.trans hσ.symm)

/-- Left composition of transporters makes the supplied stabilizer-fixed family equivariant. -/
theorem orbitUnitFamily_equivariant
    (hu : ∀ v (σ : L ≃ₐ[K] L), σ • r v = r v → σ • u v = u v) :
    ∀ (σ : L ≃ₐ[K] L) w,
      σ • orbitUnitFamily K L r hr u w = orbitUnitFamily K L r hr u (σ • w) := by
  intro σ w
  have hcomap : (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
    rw [InfinitePlace.comap_smul]
    congr 1
    ext x
    exact σ.symm.commutes x
  obtain ⟨τ, hτ⟩ : ∃ τ : L ≃ₐ[K] L, τ • r (w.comap (algebraMap K L)) = w :=
    ⟨_, (InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
      (hr (w.comap (algebraMap K L)))).choose_spec⟩
  rw [orbitUnitFamily_eq_smul K L r hr u hu w τ hτ,
    orbitUnitFamily_eq_smul K L r hr u hu (σ • w) (σ * τ) (by rw [hcomap, mul_smul, hτ]),
    hcomap, mul_smul]

/-- Transport preserves smallness at every place other than the target place. -/
theorem orbitUnitFamily_below_one
    (hu : ∀ v (w' : InfinitePlace L), w' ≠ r v → w' (u v : L) < 1) :
    ∀ w w' : InfinitePlace L, w' ≠ w →
      w' (orbitUnitFamily K L r hr u w : L) < 1 := by
  intro w w' hw'
  unfold orbitUnitFamily
  have hτ := (InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
    (hr (w.comap (algebraMap K L)))).choose_spec
  set τ := (InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
    (hr (w.comap (algebraMap K L)))).choose
  have hne : τ⁻¹ • w' ≠ r (w.comap (algebraMap K L)) := by
    intro h
    apply hw'
    rw [← hτ, ← h, smul_inv_smul]
  have key : w' ((τ • u (w.comap (algebraMap K L)) : Lˣ) : L) =
      (τ⁻¹ • w') (u (w.comap (algebraMap K L)) : L) := rfl
  rw [key]
  exact hu _ _ hne

/-- Conjugating an integer unit preserves membership in the principal-ideal kernel. -/
theorem orbitUnitFamily_mem_kernel [NumberField L]
    (hu : ∀ v, u v ∈ (toPrincipalIdeal (𝓞 L) L).ker) :
    ∀ w, orbitUnitFamily K L r hr u w ∈ (toPrincipalIdeal (𝓞 L) L).ker := by
  intro w
  unfold orbitUnitFamily
  set τ := (InfinitePlace.exists_smul_eq_of_comap_eq (w' := w)
    (hr (w.comap (algebraMap K L)))).choose
  obtain ⟨e, he⟩ :=
    (principalIdeal_eq_one_iff L _).mp (MonoidHom.mem_ker.mp (hu (w.comap (algebraMap K L))))
  rw [MonoidHom.mem_ker, principalIdeal_eq_one_iff]
  refine ⟨Units.map (RingOfIntegers.mapRingEquiv τ.toRingEquiv).toMonoidHom e, ?_⟩
  rw [← he]
  ext
  rfl

end Family

/-- Janusz's intermediate equivariant family consists of units small at every other place.
This statement includes no normalized relation or finite-index assertion. -/
theorem exists_equivariant_small_unit_family (K L : Type*)
    [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ w : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker,
      (∀ (σ : L ≃ₐ[K] L) v, σ • (w v : Lˣ) = (w (σ • v) : Lˣ)) ∧
      ∀ v v' : InfinitePlace L, v' ≠ v → v' ((w v : Lˣ) : L) < 1 := by
  choose r hr using InfinitePlace.comap_surjective (k := K) (K := L)
  choose u hu1 hu2 using fun v => exists_unit_fixed_by_stabilizer K L (r v)
  refine ⟨fun w => ⟨orbitUnitFamily K L r hr (fun v => (u v : Lˣ)) w,
    orbitUnitFamily_mem_kernel K L r hr _ (fun v => (u v).2) w⟩, ?_, ?_⟩
  · intro σ w
    exact orbitUnitFamily_equivariant K L r hr _ (fun v σ hσ => hu2 v σ hσ) σ w
  · intro w w' hw'
    exact orbitUnitFamily_below_one K L r hr _ (fun v w' hw' => hu1 v w' hw') w w' hw'

end Cox.ClassFieldTheory
