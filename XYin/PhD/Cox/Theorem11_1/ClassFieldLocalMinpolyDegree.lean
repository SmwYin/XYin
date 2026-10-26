/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Integral generator degree
Janusz V.9.3, printed175/PDF186. The statement is a source-backed native
power-basis/minimal-polynomial adapter.
-/
noncomputable section
open Polynomial
namespace Cox.ClassFieldTheory

/-- A single integral generator has the degree of its integral minimal polynomial. -/
theorem finrank_eq_natDegree_minpoly_of_adjoin_eq_top
    (R K S L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing S] [IsDomain S] [Algebra R S]
    [CommRing L] [Nontrivial L] [Algebra R L] [Algebra K L] [Algebra S L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (x : S) (hx : IsIntegral R x)
    (hgen : Algebra.adjoin K {algebraMap S L x} = ⊤) :
    Module.finrank K L = (minpoly R x).natDegree := by
  have hyK : IsIntegral K (algebraMap S L x) :=
    (hx.map (IsScalarTower.toAlgHom R S L)).tower_top
  rw [(PowerBasis.ofAdjoinEqTop hyK hgen).finrank, PowerBasis.ofAdjoinEqTop_dim,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hx, (minpoly.monic hx).natDegree_map]

end Cox.ClassFieldTheory
