/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closedness descends through faithfully flat domain extensions

For a faithfully flat algebra whose target is an integrally closed domain, the
source is integrally closed. Source domainhood follows from the actual scalar
map's injectivity. The proof extends that scalar map to fraction fields and
contracts a principal ideal through faithful flatness.

No finite, étale, Noetherian, or curve hypothesis is needed. Identity and actual
fraction-ring extensions over fields test the API. Native curve normality and
quotient geometry are separate applications.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.Normality

/-- Integral closedness descends through a faithfully flat algebra with domain target. -/
theorem isIntegrallyClosed_of_faithfullyFlat (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDomain B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A := by
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : IsDomain A := hAB.isDomain
  let g : A →+* FractionRing B := (algebraMap B (FractionRing B)).comp (algebraMap A B)
  have hg : Function.Injective g := (IsFractionRing.injective B (FractionRing B)).comp hAB
  let f : FractionRing A →+* FractionRing B := IsFractionRing.lift hg
  have hf (a : A) : f (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) :=
    IsFractionRing.lift_algebraMap hg a
  apply (isIntegrallyClosed_iff (FractionRing A)).mpr
  intro x hx
  have hcomp : (algebraMap B (FractionRing B)).comp (algebraMap A B) =
      f.comp (algebraMap A (FractionRing A)) := by
    ext a
    exact (hf a).symm
  have hxB : IsIntegral B (f x) := hx.map_of_comp_eq (algebraMap A B) f hcomp
  obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff (FractionRing B)).mp
    (inferInstance : IsIntegrallyClosed B) hxB
  obtain ⟨a, s, hs, hfrac⟩ := IsFractionRing.div_surjective A x
  have hsB : algebraMap B (FractionRing B) (algebraMap A B s) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap A B) hAB hs)
  have hmul : algebraMap A B a = algebraMap A B s * b := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul]
    have heq : algebraMap B (FractionRing B) (algebraMap A B a) /
        algebraMap B (FractionRing B) (algebraMap A B s) =
          algebraMap B (FractionRing B) b := by
      rw [← hf a, ← hf s, ← map_div₀, hfrac, hb]
    exact (div_eq_iff hsB).mp heq |>.trans (mul_comm _ _)
  have hmem : algebraMap A B a ∈
      (Ideal.span ({s} : Set A)).map (algebraMap A B) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, hmul⟩
  have ha : a ∈ Ideal.span ({s} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span ({s} : Set A))]
    exact hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨c, ?_⟩
  apply f.injective
  rw [hf, ← hfrac, map_div₀, hf a, hf s, hc, map_mul, map_mul]
  exact (mul_div_cancel_left₀ _ hsB).symm

example (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed A :=
  isIntegrallyClosed_of_faithfullyFlat A A

example (k : Type*) [Field k] : IsIntegrallyClosed k :=
  isIntegrallyClosed_of_faithfullyFlat k (FractionRing k)

#print axioms isIntegrallyClosed_of_faithfullyFlat
#print axioms Module.FaithfullyFlat.faithfulSMul
#print axioms FaithfulSMul.algebraMap_injective
#print axioms IsFractionRing.lift
#print axioms IsFractionRing.lift_algebraMap
#print axioms IsIntegral.map_of_comp_eq
#print axioms isIntegrallyClosed_iff
#print axioms IsFractionRing.div_surjective
#print axioms Ideal.comap_map_eq_self_of_faithfullyFlat
#print axioms Ideal.map_span
#print axioms Ideal.mem_span_singleton
#print axioms IsFractionRing.injective

end ModularPolynomialCurveTest.AINTLIB.Normality
