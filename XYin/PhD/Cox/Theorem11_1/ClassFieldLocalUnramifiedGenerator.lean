/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselIrreducibleReduction
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnramifiedDegree
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalMinpolyDegree
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Hensel factor lifting and the local degree comparison

Source: Janusz II.3.5 and V.9.3.
-/

noncomputable section
open Polynomial IsLocalRing
namespace Cox.ClassFieldTheory

attribute [local instance] Ideal.Quotient.field

/-- A generator satisfying a monic polynomial with separable residue defines an unramified local
extension. -/
theorem ramificationIdx_eq_one_of_separable_reduction_generator
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (x : S) (hgen : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (f : R[X]) (hf : f.Monic) (hx : aeval x f = 0)
    (hsep : (f.map (Ideal.Quotient.mk (maximalIdeal R))).Separable) :
    Ideal.ramificationIdx (maximalIdeal R) (maximalIdeal S) = 1 := by
  letI := FaithfulSMul.of_field_isFractionRing R S K L
  have hxint : IsIntegral R x := ⟨f, hf, hx⟩
  have hI : maximalIdeal R ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField
    (maximalIdeal.isMaximal R) (IsDiscreteValuationRing.not_isField R)
  obtain ⟨J, hJ, hJI⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := S) (maximalIdeal R)
  letI : J.IsMaximal := hJ
  have hJeq : J = maximalIdeal S := IsLocalRing.eq_maximalIdeal hJ
  haveI : (maximalIdeal S).LiesOver (maximalIdeal R) := hJeq ▸ hJI
  have hdiv : minpoly R x ∣ f := minpoly.isIntegrallyClosed_dvd hxint hx
  have hirr := irreducible_map_of_separable_of_adicComplete (maximalIdeal R)
    (minpoly R x) (minpoly.monic hxint) (minpoly.irreducible hxint)
    (hsep.of_dvd (Polynomial.map_dvd _ hdiv))
  apply ramificationIdx_eq_one_of_finrank_le_inertiaDeg R S K L (maximalIdeal R) hI
  rw [finrank_eq_natDegree_minpoly_of_adjoin_eq_top R K S L x hxint hgen]
  exact natDegree_le_inertiaDeg_of_irreducible_reduction
    (maximalIdeal R) (maximalIdeal S) (minpoly R x) (minpoly.monic hxint)
    hirr x (minpoly.aeval R x)

end Cox.ClassFieldTheory
