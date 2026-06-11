import Mathlib

open scoped NumberField

namespace XYin.NumberField.New

/-- A norm-Euclidean order in a number field is the full ring of integers: any order `O` whose
fraction field is the number field `K`, integral over `ℤ` and a Euclidean domain, is canonically
isomorphic (as a `ℤ`-algebra) to the ring of integers `𝓞 K`.

(A Euclidean domain is a PID, hence integrally closed, so `O` is the integral closure of `ℤ` in
`K` — i.e. the maximal order. Stated as a `ℤ`-algebra isomorphism rather than a type equality,
since `O` is only determined up to isomorphism.) -/
theorem normEuclideanOrder_eq_ringOfIntegers (O K : Type) [EuclideanDomain O] [Field K]
    [NumberField K] [Algebra O K] [IsFractionRing O K] [Algebra.IsIntegral ℤ O] :
    Nonempty (O ≃ₐ[ℤ] 𝓞 K) := by
  -- `O` carries its canonical `ℤ`-algebra structure; the scalar tower follows from the
  -- uniqueness of ring homs out of `ℤ`.
  haveI : IsScalarTower ℤ O K := IsScalarTower.of_algebraMap_eq fun n => by simp
  -- A Euclidean domain is integrally closed, and `K` is its fraction field, so the elements of
  -- `K` integral over `ℤ` are exactly those coming from `O`: `O` is the integral closure.
  haveI : IsIntegralClosure O ℤ K := by
    refine ⟨IsFractionRing.injective O K, fun {x} => ?_⟩
    rw [← IsIntegrallyClosed.isIntegral_iff (R := O)]
    exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans x hx⟩
  -- Both `O` and `𝓞 K` are integral closures of `ℤ` in `K`, hence canonically isomorphic.
  exact ⟨IsIntegralClosure.equiv ℤ O K (𝓞 K)⟩

end XYin.NumberField.New
