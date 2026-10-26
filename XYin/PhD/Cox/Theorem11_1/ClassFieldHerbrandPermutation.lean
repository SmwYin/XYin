/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHerbrandDirectSum
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section
open DirectSum
namespace Cox.CyclicCohomology

variable (R G X : Type*) [Semiring R] [Group G] [MulAction G X]

/-- The native orbit decomposition evaluates by forgetting the orbit-membership proof. -/
theorem permutation_orbitDecomposition_apply (f : X →₀ R)
    (c : MulAction.orbitRel.Quotient G X) (x : c.orbit) :
    ((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbits' G X)).trans
      (sigmaFinsuppLequivDFinsupp R)) f c x = f x := by
  rfl

/-- The native orbit decomposition preserves the actual componentwise permutation action. -/
theorem permutation_orbitDecomposition_equivariant (γ : G) (f : X →₀ R) :
    ((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbits' G X)).trans
      (sigmaFinsuppLequivDFinsupp R)) ((Representation.ofMulAction R G X) γ f) =
      (Representation.directSum (fun c : MulAction.orbitRel.Quotient G X =>
        Representation.ofMulAction R G c.orbit)) γ
        (((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbits' G X)).trans
          (sigmaFinsuppLequivDFinsupp R)) f) := by
  ext c x
  rw [permutation_orbitDecomposition_apply, Representation.ofMulAction_apply]
  change f (γ⁻¹ • (x : X)) = (Representation.ofMulAction R G c.orbit γ
    (((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbits' G X)).trans
      (sigmaFinsuppLequivDFinsupp R)) f c)) x
  rw [Representation.ofMulAction_apply, permutation_orbitDecomposition_apply]
  rfl

open scoped Classical in
/-- Source V1.5 on each orbit and V1.3 on the finite direct sum. -/
theorem herbrandQuotient_permutation_orbits
    [Fintype G] [Fintype X] (g : G) (hg : ∀ γ, γ ∈ Subgroup.zpowers g) :
    herbrandQuotient (Representation.ofMulAction ℤ G X) g =
      ∏ c : MulAction.orbitRel.Quotient G X,
        (Nat.card (MulAction.stabilizer G c.out) : ℚ)⁻¹ := by
  have horbit (c : MulAction.orbitRel.Quotient G X) :
      herbrandQuotient (Representation.ofMulAction ℤ G c.orbit) g =
        (Nat.card (MulAction.stabilizer G c.out) : ℚ)⁻¹ := by
    have hx : c.out ∈ c.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' c)
    have hstab : MulAction.stabilizer G (⟨c.out, hx⟩ : c.orbit) =
        MulAction.stabilizer G c.out := by
      ext γ
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      exact Subtype.ext_iff
    rw [herbrandQuotient_permutation g c.orbit ⟨c.out, hx⟩ hg, hstab]
  exact (herbrandQuotient_congr g _ _
      ((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbits' G X)).trans
        (sigmaFinsuppLequivDFinsupp ℤ)).toAddEquiv
      (permutation_orbitDecomposition_equivariant ℤ G X)).trans
    ((herbrandQuotient_directSum _ g hg (fun _ => finiteHerbrand_of_moduleFinite _ g hg)).trans
      (Finset.prod_congr rfl fun c _ => horbit c))

end Cox.CyclicCohomology
