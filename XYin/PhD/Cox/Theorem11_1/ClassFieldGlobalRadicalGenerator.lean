/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalUnramifiedGenerator
import XYin.PhD.Cox.Theorem11_1.ClassFieldRadicalLocalUnits

/-! # Completed generators and unramified radical extensions

Source: Janusz V.9.3 and its Hensel/local-degree prerequisites.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain Polynomial IsLocalRing
attribute [local instance] completionAlgebra completionIntegerFieldAlgebra

/-- A global radical generator is unramified at primes where its radicand and exponent are units. -/
theorem ramificationIdx_eq_one_of_radical_generator
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (n : ℕ) (hn : IsUnit (n : v.adicCompletionIntegers K))
    (a : K) (ha : v.valuation K a = 1)
    (x : L) (hgen : Algebra.adjoin K {x} = ⊤)
    (hx : x ^ n = algebraMap K L a) :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  obtain ⟨u, hu⟩ := exists_completionUnit_of_valuation_eq_one v a ha
  have hn0 : n ≠ 0 := by
    intro h
    simp [h] at hn
  apply ramificationIdx_eq_one_of_separable_local_polynomial K L v w x hgen
    (X ^ n - C (u : v.adicCompletionIntegers K)) (monic_X_pow_sub_C _ hn0)
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    change (FinitePlace.embedding w x) ^ n -
      completionEmbedding K L v w ((u : v.adicCompletionIntegers K) :
        v.adicCompletion K) = 0
    rw [← map_pow, hx, hu]
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Algebra.algebraMap_self,
      Function.comp_apply, RingHom.id_apply]
    exact sub_eq_zero.mpr (completionEmbedding_commutes K L v w a).symm
  · exact (separable_X_pow_sub_C_unit u hn).map

end Cox.ClassFieldTheory
