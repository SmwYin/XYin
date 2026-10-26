/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnramifiedGenerator
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionAdjoin
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionDegree

/-! # Completed generators and unramified radical extensions

Source: Janusz V.9.3 and its Hensel/local-degree prerequisites.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain Polynomial IsLocalRing
attribute [local instance] completionAlgebra completionIntegerFieldAlgebra
  completionIntegerAlgebra completion_integerField_isScalarTower
  completion_integerRing_isScalarTower completion_integers_isIntegralClosure
  completion_integers_finite completionIntegers_adicComplete

/-- An integral field generator with separable monic reduction gives ramification index one. -/
theorem ramificationIdx_eq_one_of_separable_reduction_fieldGenerator
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    (x : L) (hgen : Algebra.adjoin K {x} = ⊤)
    (f : R[X]) (hf : f.Monic) (hx : aeval x f = 0)
    (hsep : (f.map (Ideal.Quotient.mk (maximalIdeal R))).Separable) :
    Ideal.ramificationIdx (maximalIdeal R) (maximalIdeal S) = 1 := by
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := S)).mp
    (show IsIntegral R x from ⟨f, hf, hx⟩)
  have hyroot : aeval y f = 0 := by
    apply (IsFractionRing.injective S L)
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hy, hx]
  exact ramificationIdx_eq_one_of_separable_reduction_generator R S K L y
    (by simpa only [hy] using hgen) f hf hyroot hsep

/-- A global generator with a separable local integral polynomial is unramified at the chosen
prime. -/
theorem ramificationIdx_eq_one_of_separable_local_polynomial
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (x : L) (hgen : Algebra.adjoin K {x} = ⊤)
    (f : (v.adicCompletionIntegers K)[X]) (hf : f.Monic)
    (hx : aeval (FinitePlace.embedding w x) f = 0)
    (hsep : (f.map (Ideal.Quotient.mk
      (maximalIdeal (v.adicCompletionIntegers K)))).Separable) :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  rw [← completion_ramificationIdx_eq K L v w]
  apply ramificationIdx_eq_one_of_separable_reduction_fieldGenerator
    (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
    (v.adicCompletion K) (w.adicCompletion L) (FinitePlace.embedding w x)
      _ f hf hx hsep
  simpa only [Set.image_singleton] using completion_adjoin_image_eq_top K L v w {x} hgen

end Cox.ClassFieldTheory
