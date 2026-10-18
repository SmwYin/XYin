/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.GroupTheory.IndexNSmul

import XYin.PhD.Cox.HermiteNormalForm
import XYin.PhD.Cox.LatticeJ

/-!
# Cyclic sublattices of period lattices

The carrier is a submodule of the ambient period lattice itself. This file constructs its
canonical HNF period pair, transports it along lattice equivalences and scaling, and defines
the dual cyclic inclusion.
-/

noncomputable section

namespace PeriodPair

/-- A cyclic sublattice of index `m` in a period lattice. -/
structure CyclicSublattice (L : PeriodPair) (m : ℕ+) where
  /-- The sublattice, as a submodule of the ambient period lattice. -/
  carrier : Submodule ℤ L.lattice
  index_eq : carrier.toAddSubgroup.index = (m : ℕ)
  cyclic : IsAddCyclic (L.lattice ⧸ carrier)

namespace CyclicSublattice

variable {L : PeriodPair} {m : ℕ+}

/-- Cyclic sublattices are equal when their carriers are equal; the remaining fields are
propositions. -/
@[ext]
theorem ext {S T : CyclicSublattice L m} (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- A finite-index sublattice of a period lattice again has rank two. -/
theorem carrier_finrank (S : CyclicSublattice L m) :
    Module.finrank ℤ S.carrier = 2 := by
  letI : Module.Free ℤ L.lattice := Module.Free.of_basis L.latticeBasis
  letI : Module.Finite ℤ L.lattice := Module.Finite.of_basis L.latticeBasis
  letI : S.carrier.toAddSubgroup.FiniteIndex :=
    ⟨by rw [S.index_eq]; exact PNat.ne_zero m⟩
  calc
    Module.finrank ℤ S.carrier = Module.finrank ℤ L.lattice :=
      AddSubgroup.finrank_eq_of_finiteIndex S.carrier.toAddSubgroup
    _ = 2 := L.finrank_lattice

/-- The HNF attached to the carrier of a cyclic sublattice. -/
noncomputable def hermiteNormalForm (S : CyclicSublattice L m) :
    Module.Basis.HermiteNormalForm L.latticeBasis S.carrier :=
  S.carrier.hermiteNormalForm L.latticeBasis S.carrier_finrank

/-- The HNF matrix of a cyclic sublattice has determinant equal to its index. -/
theorem det_hermiteNormalForm_matrix (S : CyclicSublattice L m) :
    S.hermiteNormalForm.matrix.det = m := by
  rw [S.hermiteNormalForm.det_eq_index, S.index_eq]

/-- The HNF matrix of a cyclic sublattice is primitive. -/
theorem rankTwoContent_hermiteNormalForm_matrix (S : CyclicSublattice L m) :
    S.hermiteNormalForm.matrix.rankTwoContent = 1 :=
  S.hermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one.mp S.cyclic

private noncomputable def hnfPeriod (S : CyclicSublattice L m) (i : Fin 2) : ℂ :=
  (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ)

private theorem hnfPeriod_eq (S : CyclicSublattice L m) (j : Fin 2) :
    hnfPeriod S j =
      (S.hermiteNormalForm.matrix 0 j : ℂ) * L.ω₁ +
        (S.hermiteNormalForm.matrix 1 j : ℂ) * L.ω₂ := by
  have h := congrArg (fun x : L.lattice ↦ (x : ℂ))
    (L.latticeBasis.sum_repr ((S.hermiteNormalForm.bN j : S.carrier) : L.lattice)).symm
  simpa only [hnfPeriod, Fin.sum_univ_two, S.hermiteNormalForm.repr_apply,
    Submodule.coe_add, SetLike.val_smul, PeriodPair.latticeBasis_zero,
    PeriodPair.latticeBasis_one, zsmul_eq_mul] using h

private theorem hnfPeriods_linearIndependent (S : CyclicSublattice L m) :
    LinearIndependent ℝ ![hnfPeriod S 0, hnfPeriod S 1] := by
  let H := S.hermiteNormalForm.matrix
  have hdet : (H 0 0 : ℝ) * (H 1 1 : ℝ) ≠ (H 1 0 : ℝ) * (H 0 1 : ℝ) := by
    have h := S.hermiteNormalForm.isColumnHermiteNormalForm.det_pos.ne'
    rw [Matrix.det_fin_two, sub_ne_zero, mul_comm (H 0 1)] at h
    exact_mod_cast h
  have htrans := (LinearIndependent.pair_add_smul_add_smul_iff
      (R := ℝ) (S := ℝ) (x := L.ω₁) (y := L.ω₂)
      (H 0 0 : ℝ) (H 1 0 : ℝ) (H 0 1 : ℝ) (H 1 1 : ℝ)).2 ⟨L.indep, hdet⟩
  rw [hnfPeriod_eq S 0, hnfPeriod_eq S 1]
  simpa only [H, Complex.real_smul, Complex.ofReal_intCast] using htrans

/-- The canonical period pair attached to a finite-index sublattice, chosen through its HNF
basis relative to `L.latticeBasis`. -/
noncomputable def toPeriodPair (S : CyclicSublattice L m) : PeriodPair where
  ω₁ := hnfPeriod S 0
  ω₂ := hnfPeriod S 1
  indep := hnfPeriods_linearIndependent S

/-- The first period of the sublattice is the first HNF column `d ω₁`. -/
theorem toPeriodPair_ω₁ (S : CyclicSublattice L m) :
    S.toPeriodPair.ω₁ = (S.hermiteNormalForm.matrix 0 0 : ℂ) * L.ω₁ := by
  simp [toPeriodPair, hnfPeriod_eq, S.hermiteNormalForm.isColumnHermiteNormalForm.one_zero]

/-- The second period of the sublattice is the second HNF column `b ω₁ + a ω₂`. -/
theorem toPeriodPair_ω₂ (S : CyclicSublattice L m) :
    S.toPeriodPair.ω₂ = (S.hermiteNormalForm.matrix 0 1 : ℂ) * L.ω₁ +
      (S.hermiteNormalForm.matrix 1 1 : ℂ) * L.ω₂ :=
  hnfPeriod_eq S 1

/-- The chosen period pair spans exactly the embedded carrier. -/
theorem toPeriodPair_lattice (S : CyclicSublattice L m) :
    S.toPeriodPair.lattice = S.carrier.map L.lattice.subtype := by
  let f : S.carrier →ₗ[ℤ] ℂ := L.lattice.subtype.comp S.carrier.subtype
  have hspan := congrArg (Submodule.map f) S.hermiteNormalForm.bN.span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_comp,
    Submodule.range_subtype] at hspan
  have hrange : Set.range (f ∘ S.hermiteNormalForm.bN) =
      {hnfPeriod S 0, hnfPeriod S 1} := by
    ext z
    simp [Set.mem_range, Fin.exists_fin_two, f, hnfPeriod, eq_comm]
  rw [← Set.range_comp, hrange] at hspan
  simpa only [Function.comp_apply,
    PeriodPair.lattice, toPeriodPair, hnfPeriod, f, LinearMap.comp_apply,
    Submodule.subtype_apply] using hspan

/-- The `j`-invariant of the sublattice. -/
def j (S : CyclicSublattice L m) : ℂ := S.toPeriodPair.j

private def mapCarrier {M : PeriodPair} (e : L.lattice ≃ₗ[ℤ] M.lattice)
    (S : CyclicSublattice L m) : Submodule ℤ M.lattice :=
  S.carrier.map e.toLinearMap

private theorem mapCarrier_index {M : PeriodPair}
    (e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) :
    (mapCarrier e S).toAddSubgroup.index = S.carrier.toAddSubgroup.index := by
  change (S.carrier.map e.toLinearMap).toAddSubgroup.index = _
  rw [Submodule.map_toAddSubgroup]
  exact AddSubgroup.index_map_equiv S.carrier.toAddSubgroup e.toAddEquiv

private def mapQuotientEquiv {M : PeriodPair}
    (e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) :
    (L.lattice ⧸ S.carrier) ≃ₗ[ℤ] (M.lattice ⧸ mapCarrier e S) :=
  Submodule.Quotient.equiv S.carrier (mapCarrier e S) e rfl

/-- A linear equivalence of ambient lattices transports cyclic sublattices, preserving their
index and cyclic quotient. -/
noncomputable def map {M : PeriodPair} (S : CyclicSublattice L m)
    (e : L.lattice ≃ₗ[ℤ] M.lattice) : CyclicSublattice M m := by
  refine ⟨mapCarrier e S, (mapCarrier_index e S).trans S.index_eq, ?_⟩
  letI : IsAddCyclic (L.lattice ⧸ S.carrier) := S.cyclic
  exact isAddCyclic_of_surjective (mapQuotientEquiv e S)
    (mapQuotientEquiv e S).surjective

/-- Reinterpret a cyclic sublattice in a period pair with the same underlying lattice. -/
noncomputable def ofLatticeEq {M : PeriodPair} (S : CyclicSublattice L m)
    (h : L.lattice = M.lattice) : CyclicSublattice M m :=
  S.map (LinearEquiv.ofEq L.lattice M.lattice h)

@[simp]
theorem ofLatticeEq_carrier {M : PeriodPair} (S : CyclicSublattice L m)
    (h : L.lattice = M.lattice) :
    (S.ofLatticeEq h).carrier =
      S.carrier.map (LinearEquiv.ofEq L.lattice M.lattice h).toLinearMap := by
  rfl

/-- Reinterpreting the ambient period pair does not change the embedded carrier in `ℂ`. -/
theorem ofLatticeEq_carrier_map_subtype {M : PeriodPair}
    (S : CyclicSublattice L m) (h : L.lattice = M.lattice) :
    (S.ofLatticeEq h).carrier.map M.lattice.subtype =
      S.carrier.map L.lattice.subtype := by
  rw [ofLatticeEq_carrier, ← Submodule.map_comp]
  congr 1

/-- Reinterpreting the ambient period pair leaves the canonical sublattice period lattice
unchanged. -/
theorem ofLatticeEq_toPeriodPair_lattice {M : PeriodPair}
    (S : CyclicSublattice L m) (h : L.lattice = M.lattice) :
    (S.ofLatticeEq h).toPeriodPair.lattice = S.toPeriodPair.lattice := by
  rw [(S.ofLatticeEq h).toPeriodPair_lattice, S.toPeriodPair_lattice]
  exact S.ofLatticeEq_carrier_map_subtype h

/-- Reinterpreting the ambient period pair leaves the sublattice `j`-invariant unchanged. -/
theorem j_ofLatticeEq {M : PeriodPair} (S : CyclicSublattice L m)
    (h : L.lattice = M.lattice) : (S.ofLatticeEq h).j = S.j := by
  apply PeriodPair.j_congr
  exact S.ofLatticeEq_toPeriodPair_lattice h

/-- Scaling an inclusion by a nonzero complex number preserves its index and cyclic quotient. -/
noncomputable def scale (a : ℂˣ) (S : CyclicSublattice L m) :
    CyclicSublattice (a • L) m :=
  S.map (smulLatticeEquiv a L)

@[simp]
theorem scale_carrier (a : ℂˣ) (S : CyclicSublattice L m) :
    (S.scale a).carrier =
      S.carrier.map (smulLatticeEquiv a L :
        L.lattice →ₗ[ℤ] (a • L).lattice) := by
  rfl

/-- After embedding in `ℂ`, scaling the carrier is just multiplication by `a`. -/
theorem scale_carrier_map_subtype (a : ℂˣ) (S : CyclicSublattice L m) :
    (S.scale a).carrier.map (a • L).lattice.subtype =
      (S.carrier.map L.lattice.subtype).map
        (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) := by
  rw [scale_carrier, ← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- The canonical period pair of a scaled sublattice has the correspondingly scaled lattice. -/
theorem scale_toPeriodPair_lattice (a : ℂˣ) (S : CyclicSublattice L m) :
    (S.scale a).toPeriodPair.lattice = (a • S.toPeriodPair).lattice := by
  rw [(S.scale a).toPeriodPair_lattice, scale_carrier_map_subtype,
    ← S.toPeriodPair_lattice, map_lattice_mulLeftLinearEquiv]

/-- Scaling leaves the sublattice `j`-invariant unchanged. -/
theorem j_scale (a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).j = S.j := by
  change (S.scale a).toPeriodPair.j = S.toPeriodPair.j
  calc
    (S.scale a).toPeriodPair.j = (a • S.toPeriodPair).j :=
      PeriodPair.j_congr (scale_toPeriodPair_lattice a S)
    _ = S.toPeriodPair.j := PeriodPair.j_smul S.toPeriodPair a

private noncomputable def carrierEquiv (S : CyclicSublattice L m) :
    S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice :=
  (Submodule.equivSubtypeMap L.lattice S.carrier).trans
    (LinearEquiv.ofEq _ _ S.toPeriodPair_lattice.symm)

private noncomputable def transportedBasis (S : CyclicSublattice L m) :
    Module.Basis (Fin 2) ℤ S.toPeriodPair.lattice :=
  S.hermiteNormalForm.bN.map (carrierEquiv S)

private theorem transportedBasis_repr_carrierEquiv
    (S : CyclicSublattice L m) (x : S.carrier) (i : Fin 2) :
    (transportedBasis S).repr (carrierEquiv S x) i =
      S.hermiteNormalForm.bN.repr x i := by
  simp [transportedBasis]

private theorem index_nsmul_mem_carrier (S : CyclicSublattice L m)
    (x : L.lattice) : (m : ℕ) • x ∈ S.carrier := by
  have hx := S.carrier.toAddSubgroup.nsmul_index_mem x
  rwa [S.index_eq] at hx

/-- Multiplication by `m`, as a map from the ambient lattice into the sublattice. -/
private def dualLinearMap (S : CyclicSublattice L m) :
    L.lattice →ₗ[ℤ] S.toPeriodPair.lattice :=
  (carrierEquiv S).toLinearMap ∘ₗ
    LinearMap.codRestrict S.carrier ((m : ℕ) • LinearMap.id) (index_nsmul_mem_carrier S)

private theorem dualLinearMap_injective (S : CyclicSublattice L m) :
    Function.Injective (dualLinearMap S) :=
  (carrierEquiv S).injective.comp fun _ _ hxy ↦
    AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree (PNat.ne_zero m)
      (congrArg Subtype.val hxy)

private noncomputable def dualCarrier (S : CyclicSublattice L m) :
    Submodule ℤ S.toPeriodPair.lattice :=
  LinearMap.range (dualLinearMap S)

private noncomputable def dualBasis (S : CyclicSublattice L m) :
    Module.Basis (Fin 2) ℤ (dualCarrier S) :=
  L.latticeBasis.map (LinearEquiv.ofInjective (dualLinearMap S)
    (dualLinearMap_injective S))

/-- Relative to the transported HNF basis, the dual inclusion has matrix `adj H`, where `H` is
the HNF matrix of the original inclusion. -/
private theorem dualToMatrix_eq (S : CyclicSublattice L m) :
    LinearMap.toMatrix (dualBasis S) (transportedBasis S) (dualCarrier S).subtype =
      S.hermiteNormalForm.matrix.adjugate := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (transportedBasis S).repr (carrierEquiv S
    ⟨(m : ℕ) • L.latticeBasis j, index_nsmul_mem_carrier S _⟩) i = _
  have h := S.hermiteNormalForm.det_smul_repr
    ⟨(m : ℕ) • L.latticeBasis j, index_nsmul_mem_carrier S _⟩
  rw [Submodule.coe_mk, map_nsmul, Module.Basis.repr_self, Finsupp.coe_smul,
    Finsupp.single_eq_pi_single, Matrix.mulVec_smul, Matrix.mulVec_single_one,
    S.det_hermiteNormalForm_matrix] at h
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at hi
  rw [transportedBasis_repr_carrierEquiv]
  exact mul_left_cancel₀ (by exact_mod_cast PNat.ne_zero m) hi

private theorem dual_index_eq (S : CyclicSublattice L m) :
    (dualCarrier S).toAddSubgroup.index = (m : ℕ) := by
  rw [AddSubgroup.index_eq_natAbs_det (transportedBasis S)
    (dualCarrier S).toAddSubgroup (dualBasis S), Module.Basis.det_apply]
  have hmatrix : (transportedBasis S).toMatrix
      (fun i ↦ ((dualBasis S i : dualCarrier S) : S.toPeriodPair.lattice)) =
        S.hermiteNormalForm.matrix.adjugate := by
    rw [← dualToMatrix_eq]
    ext i j
    rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    rfl
  simp [hmatrix, Matrix.det_adjugate, S.det_hermiteNormalForm_matrix]

open Module.Basis.HermiteNormalForm in
private theorem dual_cyclic (S : CyclicSublattice L m) :
    IsAddCyclic (S.toPeriodPair.lattice ⧸ dualCarrier S) := by
  apply (quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one
    (transportedBasis S) (dualCarrier S) (dualBasis S)).mpr
  rw [dualToMatrix_eq, Matrix.rankTwoContent_adjugate]
  exact S.rankTwoContent_hermiteNormalForm_matrix

/-- The index `m` as a unit of `ℂ`, the scaling factor relating `mL` to `L`. -/
def indexUnit (m : ℕ+) : ℂˣ :=
  Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)

@[simp]
theorem coe_indexUnit (m : ℕ+) : ((indexUnit m : ℂˣ) : ℂ) = (m : ℂ) :=
  rfl

private theorem dualLinearMap_apply_coe (S : CyclicSublattice L m) (x : L.lattice) :
    ((dualLinearMap S x : S.toPeriodPair.lattice) : ℂ) =
      (m : ℂ) * (x : ℂ) := by
  change (((m : ℕ) • x : L.lattice) : ℂ) = _
  simp [nsmul_eq_mul]

/-- If `L' ⊂ L` is cyclic of index `m`, then `mL ⊂ L'` is again cyclic of index `m`.
This is the dual-isogeny operation used in the internal proof of symmetry. -/
noncomputable def dual (S : CyclicSublattice L m) :
    CyclicSublattice S.toPeriodPair m where
  carrier := dualCarrier S
  index_eq := dual_index_eq S
  cyclic := dual_cyclic S

/-- The dual carrier spans exactly the scaled lattice `mL`. -/
theorem dual_carrier_map_subtype (S : CyclicSublattice L m) :
    S.dual.carrier.map S.toPeriodPair.lattice.subtype = (indexUnit m • L).lattice := by
  change (dualCarrier S).map _ = _
  rw [dualCarrier, ← LinearMap.range_comp, ← map_lattice_mulLeftLinearEquiv]
  conv_rhs => rw [← L.lattice.range_subtype, ← LinearMap.range_comp]
  congr 1
  ext x
  exact dualLinearMap_apply_coe S x

/-- The period pair attached to the dual sublattice represents `mL`. -/
theorem dual_toPeriodPair_lattice (S : CyclicSublattice L m) :
    S.dual.toPeriodPair.lattice = (indexUnit m • L).lattice := by
  rw [S.dual.toPeriodPair_lattice]
  exact S.dual_carrier_map_subtype

/-- The dual sublattice `mL ⊂ L'` has the `j`-invariant of `L`. -/
theorem dual_sub_j (S : CyclicSublattice L m) : S.dual.j = L.j :=
  (PeriodPair.j_congr S.dual_toPeriodPair_lattice).trans (L.j_smul (indexUnit m))

/-- The `j`-invariant of a sublattice is that of its period pair. -/
theorem dual_base_j (S : CyclicSublattice L m) : S.toPeriodPair.j = S.j :=
  rfl

end CyclicSublattice

end PeriodPair
