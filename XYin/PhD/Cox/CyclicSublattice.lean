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

private noncomputable def hnfPeriod (S : CyclicSublattice L m) (i : Fin 2) : ℂ :=
  (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ)

private theorem hnfPeriod_eq (S : CyclicSublattice L m) (j : Fin 2) :
    hnfPeriod S j =
      (S.hermiteNormalForm.matrix 0 j : ℂ) * L.ω₁ +
        (S.hermiteNormalForm.matrix 1 j : ℂ) * L.ω₂ := by
  let h := S.hermiteNormalForm
  let v : L.lattice := S.carrier.subtype (h.bN j)
  have hv := L.latticeBasis.sum_repr v
  have hc := congrArg (fun x : L.lattice ↦ (x : ℂ)) hv.symm
  have hrepr (i : Fin 2) : L.latticeBasis.repr v i = h.matrix i j := by
    change L.latticeBasis.repr (S.carrier.subtype (h.bN j)) i = h.matrix i j
    exact h.repr_apply i j
  simp only [Fin.sum_univ_two, hrepr] at hc
  change (((h.bN j : S.carrier) : L.lattice) : ℂ) =
    (h.matrix 0 j : ℂ) * L.ω₁ + (h.matrix 1 j : ℂ) * L.ω₂
  calc
    (((h.bN j : S.carrier) : L.lattice) : ℂ) =
        ((h.matrix 0 j • L.latticeBasis 0 +
          h.matrix 1 j • L.latticeBasis 1 : L.lattice) : ℂ) := by
      simpa only [h, v] using hc
    _ = (h.matrix 0 j : ℂ) * L.ω₁ + (h.matrix 1 j : ℂ) * L.ω₂ := by
      have hcoe_add (x y : L.lattice) : ((x + y : L.lattice) : ℂ) = x + y := rfl
      have hcoe_zsmul (z : ℤ) (x : L.lattice) :
          ((z • x : L.lattice) : ℂ) = z • (x : ℂ) := rfl
      rw [hcoe_add, hcoe_zsmul, hcoe_zsmul]
      simp only [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one,
        zsmul_eq_mul]

private theorem hnfPeriods_linearIndependent (S : CyclicSublattice L m) :
    LinearIndependent ℝ ![hnfPeriod S 0, hnfPeriod S 1] := by
  let h := S.hermiteNormalForm
  have hz : h.matrix 1 0 = 0 :=
    h.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)
  have hd : h.matrix 0 0 ≠ 0 :=
    ne_of_gt (h.isColumnHermiteNormalForm.diagonal_pos 0)
  have ha : h.matrix 1 1 ≠ 0 :=
    ne_of_gt (h.isColumnHermiteNormalForm.diagonal_pos 1)
  have hdet :
      (h.matrix 0 0 : ℝ) * (h.matrix 1 1 : ℝ) ≠
        (h.matrix 1 0 : ℝ) * (h.matrix 0 1 : ℝ) := by
    rw [hz]
    simp only [Int.cast_zero, zero_mul]
    exact mul_ne_zero ((Int.cast_ne_zero (α := ℝ)).2 hd)
      ((Int.cast_ne_zero (α := ℝ)).2 ha)
  have htrans : LinearIndependent ℝ
      ![(h.matrix 0 0 : ℝ) • L.ω₁ + (h.matrix 1 0 : ℝ) • L.ω₂,
        (h.matrix 0 1 : ℝ) • L.ω₁ + (h.matrix 1 1 : ℝ) • L.ω₂] :=
    (LinearIndependent.pair_add_smul_add_smul_iff
      (R := ℝ) (S := ℝ) (x := L.ω₁) (y := L.ω₂)
      (h.matrix 0 0 : ℝ) (h.matrix 1 0 : ℝ)
      (h.matrix 0 1 : ℝ) (h.matrix 1 1 : ℝ)).2 ⟨L.indep, hdet⟩
  rw [hnfPeriod_eq S 0, hnfPeriod_eq S 1]
  simpa only [Complex.real_smul, Int.cast_ofNat] using htrans

/-- The canonical period pair attached to a finite-index sublattice, chosen through its HNF
basis relative to `L.latticeBasis`. -/
noncomputable def toPeriodPair (S : CyclicSublattice L m) : PeriodPair where
  ω₁ := hnfPeriod S 0
  ω₂ := hnfPeriod S 1
  indep := hnfPeriods_linearIndependent S

private theorem coe_carrier_add (S : CyclicSublattice L m) (u v : S.carrier) :
    ((((u + v : S.carrier) : L.lattice) : ℂ)) =
      (((u : S.carrier) : L.lattice) : ℂ) +
        (((v : S.carrier) : L.lattice) : ℂ) := rfl

private theorem coe_carrier_zsmul (S : CyclicSublattice L m)
    (a : ℤ) (u : S.carrier) :
    ((((a • u : S.carrier) : L.lattice) : ℂ)) =
      a • (((u : S.carrier) : L.lattice) : ℂ) := rfl

/-- The chosen period pair spans exactly the embedded carrier. -/
theorem toPeriodPair_lattice (S : CyclicSublattice L m) :
    S.toPeriodPair.lattice = S.carrier.map L.lattice.subtype := by
  let h := S.hermiteNormalForm
  ext x
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨a, b, hab⟩
    let y : S.carrier := a • h.bN 0 + b • h.bN 1
    refine Submodule.mem_map.mpr ⟨(y : L.lattice), y.property, ?_⟩
    change ((y : L.lattice) : ℂ) = x
    have hcoe : ((y : L.lattice) : ℂ) =
        (a : ℂ) * hnfPeriod S 0 + (b : ℂ) * hnfPeriod S 1 := by
      change (((a • h.bN 0 + b • h.bN 1 : S.carrier) : L.lattice) : ℂ) = _
      rw [coe_carrier_add, coe_carrier_zsmul, coe_carrier_zsmul]
      simp only [zsmul_eq_mul, hnfPeriod, h]
    rw [hcoe]
    simpa only [toPeriodPair] using hab
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    let y' : S.carrier := ⟨y, hy⟩
    let c := h.bN.repr y'
    refine ⟨c 0, c 1, ?_⟩
    have hb := h.bN.sum_repr y'
    have hc := congrArg
      (fun z : S.carrier ↦ (((z : S.carrier) : L.lattice) : ℂ)) hb
    simp only [Fin.sum_univ_two, coe_carrier_add,
      coe_carrier_zsmul, zsmul_eq_mul] at hc
    change (c 0 : ℂ) * hnfPeriod S 0 + (c 1 : ℂ) * hnfPeriod S 1 = (y : ℂ)
    simpa only [hnfPeriod, h, y', c] using hc

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

@[simp]
theorem map_carrier {M : PeriodPair} (S : CyclicSublattice L m)
    (e : L.lattice ≃ₗ[ℤ] M.lattice) :
    (S.map e).carrier = S.carrier.map e.toLinearMap := by
  rfl

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
  let e := (LinearEquiv.ofEq L.lattice M.lattice h : L.lattice ≃ₗ[ℤ] M.lattice)
  change (mapCarrier e S).map M.lattice.subtype =
    S.carrier.map L.lattice.subtype
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ S.carrier.map e.toLinearMap at hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨y, hy, ?_⟩
    change (y : ℂ) = ((e y : M.lattice) : ℂ)
    exact (LinearEquiv.coe_ofEq_apply h y).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, ?_⟩
    · exact Submodule.mem_map_of_mem hy
    · change ((e y : M.lattice) : ℂ) = (y : ℂ)
      exact LinearEquiv.coe_ofEq_apply h y

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
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ S.carrier.map
      (smulLatticeEquiv a L : L.lattice →ₗ[ℤ] (a • L).lattice) at hz
    rw [Submodule.mem_map] at hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨(y : ℂ), ?_, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    change z ∈ S.carrier.map L.lattice.subtype at hz
    rw [Submodule.mem_map] at hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨smulLatticeEquiv a L y, ?_, rfl⟩
    change smulLatticeEquiv a L y ∈ (S.scale a).carrier
    rw [scale_carrier]
    exact Submodule.mem_map_of_mem hy

/-- The canonical period pair of a scaled sublattice has the correspondingly scaled lattice. -/
theorem scale_toPeriodPair_lattice (a : ℂˣ) (S : CyclicSublattice L m) :
    (S.scale a).toPeriodPair.lattice = (a • S.toPeriodPair).lattice := by
  calc
    (S.scale a).toPeriodPair.lattice =
        (S.scale a).carrier.map (a • L).lattice.subtype :=
      (S.scale a).toPeriodPair_lattice
    _ = (S.carrier.map L.lattice.subtype).map
        (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) :=
      scale_carrier_map_subtype a S
    _ = S.toPeriodPair.lattice.map
        (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) := by
      rw [S.toPeriodPair_lattice]
    _ = (a • S.toPeriodPair).lattice :=
      map_lattice_mulLeftLinearEquiv a S.toPeriodPair

theorem j_scale (a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).j = S.j := by
  change (S.scale a).toPeriodPair.j = S.toPeriodPair.j
  calc
    (S.scale a).toPeriodPair.j = (a • S.toPeriodPair).j :=
      PeriodPair.j_congr (scale_toPeriodPair_lattice a S)
    _ = S.toPeriodPair.j := PeriodPair.j_smul S.toPeriodPair a

private def carrierToPeriodPairLinearMap (S : CyclicSublattice L m) :
    S.carrier →ₗ[ℤ] S.toPeriodPair.lattice where
  toFun x := ⟨((x : L.lattice) : ℂ), by
    rw [S.toPeriodPair_lattice]
    exact ⟨x, x.property, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem carrierToPeriodPairLinearMap_bijective (S : CyclicSublattice L m) :
    Function.Bijective (carrierToPeriodPairLinearMap S) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S.toPeriodPair.lattice ↦ (z : ℂ)) hxy
  · intro z
    have hz : (z : ℂ) ∈ S.carrier.map L.lattice.subtype := by
      rw [← S.toPeriodPair_lattice]
      exact z.property
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hzx

private noncomputable def carrierEquiv (S : CyclicSublattice L m) :
    S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice :=
  LinearEquiv.ofBijective (carrierToPeriodPairLinearMap S)
    (carrierToPeriodPairLinearMap_bijective S)

@[simp]
private theorem carrierEquiv_apply_coe (S : CyclicSublattice L m) (x : S.carrier) :
    ((carrierEquiv S x : S.toPeriodPair.lattice) : ℂ) =
      ((x : L.lattice) : ℂ) :=
  rfl

private noncomputable def transportedBasis (S : CyclicSublattice L m) :
    Module.Basis (Fin 2) ℤ S.toPeriodPair.lattice :=
  S.hermiteNormalForm.bN.map (carrierEquiv S)

@[simp]
private theorem transportedBasis_repr_carrierEquiv
    (S : CyclicSublattice L m) (x : S.carrier) (i : Fin 2) :
    (transportedBasis S).repr (carrierEquiv S x) i =
      S.hermiteNormalForm.bN.repr x i := by
  simp [transportedBasis]

@[simp]
private theorem transportedBasis_apply_coe (S : CyclicSublattice L m) (i : Fin 2) :
    ((transportedBasis S i : S.toPeriodPair.lattice) : ℂ) =
      (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ) := by
  simp [transportedBasis]

private def d (S : CyclicSublattice L m) : ℤ :=
  S.hermiteNormalForm.matrix 0 0

private def b (S : CyclicSublattice L m) : ℤ :=
  S.hermiteNormalForm.matrix 0 1

private def a (S : CyclicSublattice L m) : ℤ :=
  S.hermiteNormalForm.matrix 1 1

private theorem d_pos (S : CyclicSublattice L m) : 0 < d S :=
  S.hermiteNormalForm.isColumnHermiteNormalForm.diagonal_pos 0

private theorem a_pos (S : CyclicSublattice L m) : 0 < a S :=
  S.hermiteNormalForm.isColumnHermiteNormalForm.diagonal_pos 1

private theorem lower_left_eq_zero (S : CyclicSublattice L m) :
    S.hermiteNormalForm.matrix 1 0 = 0 :=
  S.hermiteNormalForm.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)

@[simp]
private theorem hermite_repr_apply (S : CyclicSublattice L m) (i j : Fin 2) :
    L.latticeBasis.repr
      (((S.hermiteNormalForm.bN j : S.carrier) : L.lattice)) i =
        S.hermiteNormalForm.matrix i j :=
  S.hermiteNormalForm.repr_apply i j

private theorem originalMatrix_eq (S : CyclicSublattice L m) :
    S.hermiteNormalForm.matrix = !![d S, b S; 0, a S] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d, b, a, lower_left_eq_zero S]

private theorem d_mul_a_eq_m (S : CyclicSublattice L m) :
    d S * a S = (m : ℤ) := by
  have hdetabs : S.hermiteNormalForm.matrix.det.natAbs = (m : ℕ) := by
    rw [← S.index_eq]
    exact S.hermiteNormalForm.index_eq_natAbs_det.symm
  rw [originalMatrix_eq] at hdetabs
  rw [Matrix.det_fin_two_of] at hdetabs
  simp only [mul_zero, sub_zero] at hdetabs
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hdetabs
  simpa [Int.natCast_natAbs, abs_of_pos (mul_pos (d_pos S) (a_pos S))] using hcast

private theorem index_nsmul_mem_carrier (S : CyclicSublattice L m)
    (x : L.lattice) : (m : ℕ) • x ∈ S.carrier := by
  have hx := S.carrier.toAddSubgroup.nsmul_index_mem x
  rwa [S.index_eq] at hx

private def dualLinearMap (S : CyclicSublattice L m) :
    L.lattice →ₗ[ℤ] S.toPeriodPair.lattice where
  toFun x := carrierEquiv S ⟨(m : ℕ) • x, index_nsmul_mem_carrier S x⟩
  map_add' x y := by
    rw [← map_add]
    apply congrArg (carrierEquiv S)
    apply Subtype.ext
    simp
  map_smul' z x := by
    rw [← map_smul]
    apply congrArg (carrierEquiv S)
    apply Subtype.ext
    exact smul_comm (m : ℕ) z x

private theorem dualLinearMap_injective (S : CyclicSublattice L m) :
    Function.Injective (dualLinearMap S) := by
  intro x y hxy
  have hxy' := (carrierEquiv S).injective hxy
  have hxy'' : (m : ℕ) • x = (m : ℕ) • y := Subtype.ext_iff.mp hxy'
  exact AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree
    (PNat.ne_zero m) hxy''

private noncomputable def dualCarrier (S : CyclicSublattice L m) :
    Submodule ℤ S.toPeriodPair.lattice :=
  LinearMap.range (dualLinearMap S)

private noncomputable def dualBasis (S : CyclicSublattice L m) :
    Module.Basis (Fin 2) ℤ (dualCarrier S) :=
  L.latticeBasis.map (LinearEquiv.ofInjective (dualLinearMap S)
    (dualLinearMap_injective S))

private def dualMatrix (S : CyclicSublattice L m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a S, -b S; 0, d S]

private theorem nsmul_basis_zero_repr_zero (S : CyclicSublattice L m) :
    L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 0 =
      L.latticeBasis.repr
        (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 0 := by
  simp
  simpa [d, a, mul_comm] using (d_mul_a_eq_m S).symm

private theorem nsmul_basis_zero_repr_one (S : CyclicSublattice L m) :
    L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 1 =
      L.latticeBasis.repr
        (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 1 := by
  simp [lower_left_eq_zero S]

private theorem nsmul_basis_zero_eq (S : CyclicSublattice L m) :
    (⟨(m : ℕ) • L.latticeBasis 0, index_nsmul_mem_carrier S _⟩ : S.carrier) =
      a S • S.hermiteNormalForm.bN 0 := by
  apply Subtype.ext
  apply L.latticeBasis.repr.injective
  ext i
  fin_cases i
  · exact nsmul_basis_zero_repr_zero S
  · exact nsmul_basis_zero_repr_one S

private theorem nsmul_basis_one_repr_zero (S : CyclicSublattice L m) :
    L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 0 =
      L.latticeBasis.repr
        (((-b S • S.hermiteNormalForm.bN 0 +
          d S • S.hermiteNormalForm.bN 1 : S.carrier) : L.lattice)) 0 := by
  simp only [Fin.isValue, map_nsmul, Module.Basis.repr_self,
    Finsupp.smul_single, Int.nsmul_eq_mul, mul_one, ne_eq,
    zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne,
    _root_.neg_smul, Submodule.coe_add, NegMemClass.coe_neg,
    SetLike.val_smul, map_add, map_neg, map_smul, Finsupp.coe_add,
    Finsupp.coe_neg, Finsupp.coe_smul, zsmul_eq_mul, Pi.add_apply,
    Pi.neg_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq,
    hermite_repr_apply]
  change (0 : ℤ) = -(b S * d S) + d S * b S
  ring

private theorem nsmul_basis_one_repr_one (S : CyclicSublattice L m) :
    L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 1 =
      L.latticeBasis.repr
        (((-b S • S.hermiteNormalForm.bN 0 +
          d S • S.hermiteNormalForm.bN 1 : S.carrier) : L.lattice)) 1 := by
  simp only [Fin.isValue, map_nsmul, Module.Basis.repr_self,
    Finsupp.smul_single, Int.nsmul_eq_mul, mul_one,
    Finsupp.single_eq_same, _root_.neg_smul, Submodule.coe_add,
    NegMemClass.coe_neg, SetLike.val_smul, map_add, map_neg, map_smul,
    Finsupp.coe_add, Finsupp.coe_neg, Finsupp.coe_smul, zsmul_eq_mul,
    Pi.add_apply, Pi.neg_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, hermite_repr_apply, lower_left_eq_zero S, mul_zero,
    neg_zero, zero_add]
  simpa [d, a] using (d_mul_a_eq_m S).symm

private theorem nsmul_basis_one_eq (S : CyclicSublattice L m) :
    (⟨(m : ℕ) • L.latticeBasis 1, index_nsmul_mem_carrier S _⟩ : S.carrier) =
      -b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1 := by
  apply Subtype.ext
  apply L.latticeBasis.repr.injective
  ext i
  fin_cases i
  · exact nsmul_basis_one_repr_zero S
  · exact nsmul_basis_one_repr_one S

private theorem dualLinearMap_basis_zero_eq (S : CyclicSublattice L m) :
    dualLinearMap S (L.latticeBasis 0) =
      carrierEquiv S (a S • S.hermiteNormalForm.bN 0) := by
  change carrierEquiv S
      ⟨(m : ℕ) • L.latticeBasis 0, index_nsmul_mem_carrier S _⟩ = _
  exact congrArg (carrierEquiv S) (nsmul_basis_zero_eq S)

private theorem dualLinearMap_basis_one_eq (S : CyclicSublattice L m) :
    dualLinearMap S (L.latticeBasis 1) = carrierEquiv S
      (-b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1) := by
  change carrierEquiv S
      ⟨(m : ℕ) • L.latticeBasis 1, index_nsmul_mem_carrier S _⟩ = _
  exact congrArg (carrierEquiv S) (nsmul_basis_one_eq S)

private theorem dual_repr_zero_zero (S : CyclicSublattice L m) :
    (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 0 =
      dualMatrix S 0 0 := by
  rw [dualLinearMap_basis_zero_eq, transportedBasis_repr_carrierEquiv]
  simp only [Fin.isValue, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, Int.zsmul_eq_mul, mul_one,
    Finsupp.single_eq_same, dualMatrix, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]

private theorem dual_repr_one_zero (S : CyclicSublattice L m) :
    (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 1 =
      dualMatrix S 1 0 := by
  rw [dualLinearMap_basis_zero_eq, transportedBasis_repr_carrierEquiv]
  simp only [Fin.isValue, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, Int.zsmul_eq_mul, mul_one, ne_eq,
    one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne,
    dualMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]

private theorem dual_repr_zero_one (S : CyclicSublattice L m) :
    (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 0 =
      dualMatrix S 0 1 := by
  rw [dualLinearMap_basis_one_eq, transportedBasis_repr_carrierEquiv]
  simp only [Fin.isValue, _root_.neg_smul, map_add, map_neg, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, Int.zsmul_eq_mul,
    mul_one, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, Finsupp.single_eq_same, ne_eq, zero_ne_one,
    not_false_eq_true, Finsupp.single_eq_of_ne, add_zero, dualMatrix,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero]

private theorem dual_repr_one_one (S : CyclicSublattice L m) :
    (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 1 =
      dualMatrix S 1 1 := by
  rw [dualLinearMap_basis_one_eq, transportedBasis_repr_carrierEquiv]
  simp only [Fin.isValue, _root_.neg_smul, map_add, map_neg, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, Int.zsmul_eq_mul,
    mul_one, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ne_eq, one_ne_zero, not_false_eq_true,
    Finsupp.single_eq_of_ne, neg_zero, Finsupp.single_eq_same, zero_add,
    dualMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

private theorem dualToMatrix_eq (S : CyclicSublattice L m) :
    LinearMap.toMatrix (dualBasis S) (transportedBasis S) (dualCarrier S).subtype =
      dualMatrix S := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (transportedBasis S).repr (dualLinearMap S (L.latticeBasis j)) i = _
  fin_cases i <;> fin_cases j
  · exact dual_repr_zero_zero S
  · exact dual_repr_zero_one S
  · exact dual_repr_one_zero S
  · exact dual_repr_one_one S

private theorem dual_index_eq (S : CyclicSublattice L m) :
    (dualCarrier S).toAddSubgroup.index = (m : ℕ) := by
  rw [AddSubgroup.index_eq_natAbs_det (transportedBasis S)
    (dualCarrier S).toAddSubgroup (dualBasis S), Module.Basis.det_apply]
  have hmatrix : (transportedBasis S).toMatrix
      (fun i ↦ ((dualBasis S i : dualCarrier S) : S.toPeriodPair.lattice)) =
        dualMatrix S := by
    rw [← dualToMatrix_eq]
    ext i j
    rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    rfl
  rw [hmatrix]
  rw [show (dualMatrix S).det = a S * d S by
    simp [dualMatrix, Matrix.det_fin_two_of]]
  rw [mul_comm, d_mul_a_eq_m]
  simp

private theorem dual_content_eq_one (S : CyclicSublattice L m) :
    Matrix.rankTwoContent (dualMatrix S) = 1 := by
  have horiginal : Matrix.rankTwoContent S.hermiteNormalForm.matrix = 1 :=
    S.hermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one.mp S.cyclic
  rw [originalMatrix_eq] at horiginal
  simpa [Matrix.rankTwoContent, dualMatrix, d, b, a, Nat.gcd_comm,
    Nat.gcd_left_comm, Nat.gcd_assoc] using horiginal

open Module.Basis.HermiteNormalForm in
private theorem dual_cyclic (S : CyclicSublattice L m) :
    IsAddCyclic (S.toPeriodPair.lattice ⧸ dualCarrier S) := by
  apply (quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one
    (transportedBasis S) (dualCarrier S) (dualBasis S)).mpr
  simpa only [dualToMatrix_eq] using dual_content_eq_one S

private def indexUnit (m : ℕ+) : ℂˣ :=
  Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)

@[simp]
private theorem dualLinearMap_apply_coe (S : CyclicSublattice L m) (x : L.lattice) :
    ((dualLinearMap S x : S.toPeriodPair.lattice) : ℂ) =
      (m : ℂ) * (x : ℂ) := by
  change (((m : ℕ) • x : L.lattice) : ℂ) = _
  simp [nsmul_eq_mul]

private theorem dualCarrier_map_subtype_aux (S : CyclicSublattice L m) :
    (dualCarrier S).map S.toPeriodPair.lattice.subtype =
      (indexUnit m • L).lattice := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, rfl⟩ := hy
    change ((dualLinearMap S x : S.toPeriodPair.lattice) : ℂ) ∈
      (indexUnit m • L).lattice
    rw [dualLinearMap_apply_coe]
    exact L.mem_smul_lattice.mpr ⟨x, x.property, by simp [indexUnit]⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := L.mem_smul_lattice.mp hz
    let xL : L.lattice := ⟨x, hx⟩
    refine Submodule.mem_map.mpr ⟨dualLinearMap S xL, ?_, ?_⟩
    · exact LinearMap.mem_range_self (dualLinearMap S) xL
    · change ((dualLinearMap S xL : S.toPeriodPair.lattice) : ℂ) =
        (indexUnit m : ℂ) * x
      rw [dualLinearMap_apply_coe]
      simp [xL, indexUnit]

/-- If `L' ⊂ L` is cyclic of index `m`, then `mL ⊂ L'` is again cyclic of index `m`.
This is the dual-isogeny operation used in the internal proof of symmetry. -/
noncomputable def dual (S : CyclicSublattice L m) :
    CyclicSublattice S.toPeriodPair m where
  carrier := dualCarrier S
  index_eq := dual_index_eq S
  cyclic := dual_cyclic S

/-- The dual carrier spans exactly the scaled lattice `mL`. -/
theorem dual_carrier_map_subtype (S : CyclicSublattice L m) :
    S.dual.carrier.map S.toPeriodPair.lattice.subtype =
      ((Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)) • L).lattice := by
  change (dualCarrier S).map S.toPeriodPair.lattice.subtype =
    (indexUnit m • L).lattice
  exact dualCarrier_map_subtype_aux S

/-- The period pair attached to the dual sublattice represents `mL`. -/
theorem dual_toPeriodPair_lattice (S : CyclicSublattice L m) :
    S.dual.toPeriodPair.lattice =
      ((Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)) • L).lattice := by
  rw [S.dual.toPeriodPair_lattice]
  exact S.dual_carrier_map_subtype

theorem dual_sub_j (S : CyclicSublattice L m) : S.dual.j = L.j := by
  let u : ℂˣ := Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)
  change S.dual.toPeriodPair.j = L.j
  calc
    S.dual.toPeriodPair.j = (u • L).j := by
      apply PeriodPair.j_congr
      simpa only [u] using S.dual_toPeriodPair_lattice
    _ = L.j := L.j_smul u

theorem dual_base_j (S : CyclicSublattice L m) : S.toPeriodPair.j = S.j := by
  rfl

end CyclicSublattice

end PeriodPair
