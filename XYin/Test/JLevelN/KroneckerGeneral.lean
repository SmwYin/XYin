import XYin.Test.JLevelN.Theorem1118
import XYin.Test.JLevelN.QExpansion1113

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries Polynomial
open scoped Manifold

/-!
# Cox Theorem 11.18(v): Kronecker's congruence (skeleton)

Cox pp. 233–234.  For `m = p` prime, `C(p) = {(1 i; 0 p) : 0 ≤ i < p} ∪ {(p 0; 0 1)}`, and
working mod `(1−ζ_p)` in `ℤ[ζ_p]((q^{1/p}))`:
* (11.20) `j(σ_i τ) ≡ j(σ_0 τ) (mod 1−ζ_p)` for `0 ≤ i ≤ p−1`  (`ζ_p ≡ 1`);
* (11.21) `j(σ_p τ) ≡ j(τ)^p (mod 1−ζ_p)`  (Frobenius `c_n^p ≡ c_n`, then `(1−ζ_p) ∣ p`);
hence `Φ_p(X, j) ≡ (X^p − j)(X − j^p) (mod 1−ζ_p)`, whose integer coefficient differences are
divisible by `(1−ζ_p)` hence by `p` (Exercise 11.13), and the Hasse principle lifts this to
`Φ_p(X,Y) ≡ (X^p − Y)(X − Y^p) (mod p)`.

This skeleton proves the clean Frobenius step on the integer coefficients and states the two
number-theoretic leaves (the `(1−ζ_p) ∣ p` integer-divisibility, Exercise 11.13) with the
cyclotomic setup as hypotheses.  The mod-`(1−ζ_p)` series congruences (11.20)/(11.21) and the
final assembly remain the next decomposition target.
-/

noncomputable section

section Frobenius

/-- Frobenius on the integer `j`-coefficients (Cox p. 233, `c_n^p ≡ c_n mod p`), the engine
of (11.21).  Immediate from `ZMod.pow_card`. -/
theorem jIntCoeff_pow_card (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (jIntCoeff n : ZMod p) ^ p = (jIntCoeff n : ZMod p) :=
  ZMod.pow_card _

end Frobenius

section OneSubZeta

open NumberField

/-- **Exercise 11.13** (the integer-divisibility step of (v)).  A rational integer whose image
in `ℤ[ζ_p]` is divisible by `(1 − ζ_p)` is divisible by `p`.  Uses `(1 − ζ_p) ∣ p` via
`IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'` (norm `= p`, verified in mathlib for
`p ≠ 2`; `p = 2` is the already-proved `LevelTwo` case). -/
theorem int_dvd_of_oneSubZeta_dvd {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (z : ℤ)
    (hdvd : (hζ.toInteger - 1) ∣ (z : 𝓞 K)) : (p : ℤ) ∣ z := by
  -- (1-ζ) ∣ z ⟹ N(1-ζ) ∣ N(z); N(ζ-1) = p, N(z) = z^[K:ℚ]; so p ∣ z^k ⟹ p ∣ z (p prime).
  have hnd := map_dvd (Algebra.norm ℤ) hdvd
  rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' hp] at hnd
  rw [show ((z : 𝓞 K)) = algebraMap ℤ (𝓞 K) z from (eq_intCast (algebraMap ℤ (𝓞 K)) z).symm,
    Algebra.norm_algebraMap] at hnd
  exact (Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow hnd

end OneSubZeta

section Assembly

/-- **Cox Theorem 11.18(v)** (assembly target, mirrors `Theorem1118.modularPolynomial_kronecker`).
Follows from (11.20)/(11.21) mod `(1−ζ_p)`, `int_dvd_of_oneSubZeta_dvd`, and the Hasse
principle. -/
theorem modularPolynomial_kronecker_general (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (modularPolynomial p).map (Polynomial.mapRingHom (Int.castRingHom (ZMod (p : ℕ)))) =
      (Polynomial.C (Polynomial.X ^ (p : ℕ)) - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ (p : ℕ)) := by
  sorry -- T019: mod-(1-ζ_p) congruences (11.20)/(11.21) need ℤ[ζ_p] series + Hasse (T007) + T018. Substantial.

end Assembly
