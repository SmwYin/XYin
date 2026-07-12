import XYin.PhD.Cox.ModularPolynomial

/-!
# Cyclic sublattices and Cox Theorem 11.23

The carrier is a submodule of the ambient period lattice itself.  This avoids storing an
arbitrary second period basis and makes Lemma 11.24 a genuine equivalence with the canonical
HNF representatives `CoxMatrix m`.
-/

open MatrixGroups UpperHalfPlane

noncomputable section

namespace PeriodPair

/-- A cyclic sublattice of index `m` in a period lattice. -/
structure CyclicSublattice (L : PeriodPair) (m : ℕ+) where
  carrier : Submodule ℤ L.lattice
  index_eq : carrier.toAddSubgroup.index = (m : ℕ)
  cyclic : IsAddCyclic (L.lattice ⧸ carrier)

namespace CyclicSublattice

variable {L : PeriodPair} {m : ℕ+}

/-- The canonical period pair attached to a finite-index sublattice, chosen through its HNF
basis relative to `L.latticeBasis`. -/
noncomputable def toPeriodPair (S : CyclicSublattice L m) : PeriodPair := by
  sorry

/-- The chosen period pair spans exactly the embedded carrier. -/
theorem toPeriodPair_lattice (S : CyclicSublattice L m) :
    S.toPeriodPair.lattice = S.carrier.map L.lattice.subtype := by
  sorry

/-- The `j`-invariant of the sublattice. -/
def j (S : CyclicSublattice L m) : ℂ := S.toPeriodPair.j

/-- The HNF attached to the carrier of a cyclic sublattice. -/
noncomputable def hermiteNormalForm (S : CyclicSublattice L m) :
    Module.Basis.HermiteNormalForm L.latticeBasis S.carrier := by
  sorry

/-- Scaling an inclusion by a nonzero complex number preserves its index and cyclic quotient. -/
noncomputable def scale (a : ℂˣ) (S : CyclicSublattice L m) :
    CyclicSublattice (a • L) m := by
  sorry

theorem j_scale (a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).j = S.j := by
  sorry

/-- If `L' ⊂ L` is cyclic of index `m`, then `mL ⊂ L'` is again cyclic of index `m`.
This is the dual-isogeny operation used in the internal proof of symmetry. -/
noncomputable def dual (S : CyclicSublattice L m) :
    CyclicSublattice S.toPeriodPair m := by
  sorry

theorem dual_sub_j (S : CyclicSublattice L m) : S.dual.j = L.j := by
  sorry

theorem dual_base_j (S : CyclicSublattice L m) : S.toPeriodPair.j = S.j := by
  sorry

end CyclicSublattice

end PeriodPair

namespace Cox

/-- The carrier `[d,aτ+b]` associated to a Cox representative. -/
noncomputable def CoxMatrix.sublattice {m : ℕ+} (σ : CoxMatrix m) (τ : ℍ) :
    Submodule ℤ (UpperHalfPlane.periodPair τ).lattice := by
  sorry

/-- The converse half of Lemma 11.24: a Cox representative produces a cyclic index-`m`
sublattice. -/
noncomputable def CoxMatrix.toCyclicSublattice {m : ℕ+} (σ : CoxMatrix m) (τ : ℍ) :
    PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m := by
  sorry

/-- Cox Lemma 11.24: cyclic index-`m` sublattices of `[1,τ]` are uniquely classified by
`C(m)`. -/
noncomputable def cyclicSublatticeEquivCoxMatrix (m : ℕ+) (τ : ℍ) :
    PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m ≃ CoxMatrix m := by
  sorry

/-- The HNF inclusion matrix of a cyclic sublattice is `!![d,b;0,a]` for its unique Cox
representative. -/
theorem cyclicSublattice_hnf_matrix (m : ℕ+) (τ : ℍ)
    (S : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m) :
    S.hermiteNormalForm.matrix =
      (cyclicSublatticeEquivCoxMatrix m τ S).inclusionMatrix := by
  sorry

/-- The lattice of the sublattice classified by `σ` is `[d,aτ+b] = d[1,στ]`. -/
theorem coxMatrix_toPeriodPair_lattice (m : ℕ+) (τ : ℍ) (σ : CoxMatrix m) :
    (σ.toCyclicSublattice τ).toPeriodPair.lattice =
      (((Units.mk0 (σ.d : ℂ) (by exact_mod_cast σ.d_pos.ne')) •
        UpperHalfPlane.periodPair (σ.act τ)).lattice) := by
  sorry

/-- Root classification over a normalized lattice, the local form of Theorem 11.23. -/
theorem modularPolynomialC_zero_iff_normalizedCyclicSublattice
    (m : ℕ+) (τ : ℍ) (u : ℂ) :
    (modularPolynomialC m).eval u (j τ) = 0 ↔
      ∃ S : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m,
        u = S.j := by
  sorry

/-- Cox Theorem 11.23: zeros of `Φ_m` classify cyclic index-`m` lattice inclusions. -/
theorem theorem_11_23 (m : ℕ+) (u v : ℂ) :
    (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval u v = 0 ↔
      ∃ L : PeriodPair, ∃ S : PeriodPair.CyclicSublattice L m,
        u = S.j ∧ v = L.j := by
  sorry

end Cox
