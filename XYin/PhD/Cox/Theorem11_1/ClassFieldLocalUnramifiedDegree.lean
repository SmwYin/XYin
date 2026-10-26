/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite

/-! # Hensel factor lifting and the local degree comparison

Source: Janusz II.3.5 and V.9.3.
-/

noncomputable section
open Polynomial IsLocalRing
namespace Cox.ClassFieldTheory

attribute [local instance] Ideal.Quotient.field

/-- An irreducible residue polynomial with an actual lifted root has degree bounded by the
residue extension. -/
theorem natDegree_le_inertiaDeg_of_irreducible_reduction
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (I : Ideal R) [I.IsMaximal] (J : Ideal S) [J.LiesOver I]
    (f : R[X]) (hf : f.Monic)
    (hirr : Irreducible (f.map (Ideal.Quotient.mk I)))
    (x : S) (hx : aeval x f = 0) :
    f.natDegree ≤ Ideal.inertiaDeg I J := by
  have hJ : J ≠ ⊤ := by
    intro h
    have hover := J.over_def I
    rw [h, Ideal.under_def, Ideal.comap_top] at hover
    exact Ideal.IsMaximal.ne_top inferInstance hover
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hroot : aeval (Ideal.Quotient.mk J x) (f.map (Ideal.Quotient.mk I)) = 0 := by
    rw [show Ideal.Quotient.mk I = algebraMap R (R ⧸ I) from rfl, Polynomial.aeval_map_algebraMap,
      show Ideal.Quotient.mk J x = Ideal.Quotient.mkₐ R J x from rfl,
      Polynomial.aeval_algHom_apply, hx, map_zero]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot (hf.map _)
  rw [Ideal.inertiaDeg_algebraMap, ← hf.natDegree_map (Ideal.Quotient.mk I), hmin]
  exact minpoly.natDegree_le _

/-- The fundamental local degree identity forces ramification index one once inertia degree
reaches field degree. -/
theorem ramificationIdx_eq_one_of_finrank_le_inertiaDeg
    (R S K L : Type*) [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (I : Ideal R) [I.IsMaximal] (hI : I ≠ ⊥)
    (hdegree : Module.finrank K L ≤ Ideal.inertiaDeg I (maximalIdeal S)) :
    Ideal.ramificationIdx I (maximalIdeal S) = 1 := by
  haveI := FaithfulSMul.of_field_isFractionRing R S K L
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := S) I
  haveI := hQ.1
  haveI := hQ.2
  have hQmax : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) Q
    (by rw [← Ideal.under_def, ← hQ.2.over]; infer_instance)
  have hQeq : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal hQmax
  subst hQeq
  have hef := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := S) (K := K) (L := L) hI
  have hf : 0 < Ideal.inertiaDeg I (maximalIdeal S) := Ideal.inertiaDeg_pos I (maximalIdeal S)
  have he : Ideal.ramificationIdx I (maximalIdeal S) ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (maximalIdeal S) hI
  rw [← hef] at hdegree
  have hle : Ideal.ramificationIdx I (maximalIdeal S) ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by rw [one_mul]; exact hdegree) hf
  omega

end Cox.ClassFieldTheory
