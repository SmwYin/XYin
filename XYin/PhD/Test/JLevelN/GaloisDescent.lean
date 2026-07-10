import XYin.PhD.Test.JLevelN.QExpansion1113
import XYin.PhD.Test.JLevelN.HasseQPrinciple

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries Polynomial
open scoped Manifold

/-!
# Galois descent for Cox Theorem 11.18(i) (skeleton, G4)

Cox pp. 231–232.  The Galois group of `ℚ(ζ_m)/ℚ` acts on the coefficients of the formal
Laurent series and permutes the `{j(στ) : σ ∈ C(m)}` via `σ = (a b; 0 d) ↦ (a, b', d)` with
`b' ≡ bk (mod d)` (where `ψ(ζ_m) = ζ_m^k`).  Symmetric functions are therefore Galois-fixed,
hence lie in `ℚ((q^{1/m}))`; being `SL₂(ℤ)`-periodic with algebraic-integer coefficients they
lie in `ℤ((q))`.

This file isolates:
* the **combinatorial core** `cmReindex` (the permutation of `C(m)`, pure number theory), and
* the **pivotal integrality leaf** `coxPhiFunction_coeff_integer_qExpansion` feeding the Hasse
  principle to give Theorem 11.18(i).
-/

namespace Test

open UpperHalfPlane

noncomputable section

section CMReindex

variable {m : ℕ+}

/-- The reindexing `σ = (a b; 0 d) ↦ (a, b·k mod d, d)` induced by `k` coprime to `m`
(Cox p. 232: `b' ≡ bk (mod d)`).  This is the permutation of `C(m)` realised by the Galois
automorphism `ψ(ζ_m) = ζ_m^k`. -/
def cmReindex (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) (σ : CM m) : CM m where
  a := σ.a
  b := σ.b * k % σ.d
  d := σ.d
  ha := σ.ha
  had := σ.had
  hb := Nat.mod_lt _ σ.d_pos
  hgcd := by
    have hga : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ σ.a :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hgb' : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ σ.b * k % σ.d :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hgd : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ σ.d := Nat.gcd_dvd_right _ _
    have hgm : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ (m : ℕ) := hgd.trans σ.d_dvd
    have hgbk : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ σ.b * k := by
      have hdm := Nat.div_add_mod (σ.b * k) σ.d
      have h2 := Nat.dvd_add (hgd.mul_right (σ.b * k / σ.d)) hgb'
      rwa [hdm] at h2
    have hcop : Nat.Coprime (Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d) k :=
      (hk.coprime_dvd_right hgm).symm
    have hgb : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣ σ.b :=
      hcop.dvd_of_dvd_mul_right hgbk
    have hfin : Nat.gcd (Nat.gcd σ.a (σ.b * k % σ.d)) σ.d ∣
        Nat.gcd (Nat.gcd σ.a σ.b) σ.d :=
      Nat.dvd_gcd (Nat.dvd_gcd hga hgb) hgd
    rw [σ.hgcd] at hfin
    exact Nat.dvd_one.mp hfin

/-- `cmReindex` preserves `a` and `d`. -/
theorem cmReindex_a (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) (σ : CM m) :
    (cmReindex k hk σ).a = σ.a := rfl

theorem cmReindex_d (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) (σ : CM m) :
    (cmReindex k hk σ).d = σ.d := rfl

/-- For `k` coprime to `m`, `cmReindex k` is a bijection of `C(m)` (Cox: Galois permutes the
`j(στ)`). -/
theorem cmReindex_bijective (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    Function.Bijective (cmReindex k hk) := by
  apply Finite.injective_iff_bijective.mp
  intro σ σ' h
  have ha : σ.a = σ'.a := by simpa [cmReindex] using congrArg CM.a h
  have hd : σ.d = σ'.d := by simpa [cmReindex] using congrArg CM.d h
  have hb : σ.b * k % σ.d = σ'.b * k % σ'.d := by simpa [cmReindex] using congrArg CM.b h
  rw [← hd] at hb
  have hkd : Nat.Coprime k σ.d := hk.coprime_dvd_right σ.d_dvd
  have hmod : σ.b ≡ σ'.b [MOD σ.d] := Nat.ModEq.cancel_right_of_coprime hkd.symm hb
  have hbeq : σ.b = σ'.b := by
    have h1 := Nat.mod_eq_of_lt σ.hb
    have h2 := Nat.mod_eq_of_lt (hd ▸ σ'.hb)
    rwa [Nat.ModEq, h1, h2] at hmod
  apply CM.toFin_injective
  simp only [CM.toFin, Prod.mk.injEq, Fin.mk.injEq]
  exact ⟨ha, hbeq, hd⟩

end CMReindex

section IntegerQExpansion

/-- **Pivotal leaf for Cox Theorem 11.18(i)** (Cox pp. 231–232).  Each coefficient of the
function-valued Cox product `coxPhiFunction m` — an elementary symmetric function of the
`{j(στ)}` — has an **integer** q-expansion.

Cox's proof: the coefficient lies in `ℚ(ζ_m)((q^{1/m}))` (via (11.13)); the Galois action
(`cmReindex`) fixes it, so it lies in `ℚ((q^{1/m}))`; `SL₂(ℤ)`-periodicity gives integral
`q`-powers and algebraic-integer coefficients, hence rational integers.  Together with
`HasseQPrinciple.hasse_qExpansion_principle` and
`coxPhiFunction_coeff_polynomialInJ_of_meromorphic`, this yields Theorem 11.18(i). -/
theorem coxPhiFunction_coeff_integer_qExpansion (m : ℕ+) (n : ℕ) :
    ∀ k : ℤ, ∃ z : ℤ,
      (laurentqExpansion 1 ((coxPhiFunction m).coeff n)).coeff k = (z : ℂ) := by
  sorry -- T012: Galois-fixed-field descent; needs laurentqExpansion algebra-hom API (absent) + ring-hom coeff map. Substantial.

end IntegerQExpansion

end

end Test
