import XYin.PhD.Test.JLevelN.Existence

open UpperHalfPlane

/-!
# Cox `C(m)` and Lemma 11.11 (skeleton, G1)

This file introduces Cox's set `C(m)` of upper-triangular integer matrices (Cox p. 228)
as a structure `CM m` on the triple `(a,b,d)`, equips it with `DecidableEq`/`Fintype`, and
states **Cox Lemma 11.11**: `C(m)` is in bijection with the right cosets of `Γ₀(m)` used by
the existing `coxPhiFunction`.  The bijection itself (and the matrix construction behind it)
is the load-bearing leaf, left as `sorry`.
-/

noncomputable section

/-- **Cox `C(m)`** (Cox p. 228): integer matrices `(a b; 0 d)` with `ad = m`, `a > 0`,
`0 ≤ b < d`, `gcd(a,b,d) = 1`, encoded by the triple `(a,b,d)`. -/
structure CM (m : ℕ+) where
  a : ℕ
  b : ℕ
  d : ℕ
  ha : 0 < a
  had : a * d = (m : ℕ)
  hb : b < d
  hgcd : Nat.gcd (Nat.gcd a b) d = 1

namespace CM

variable {m : ℕ+}

theorem d_pos (σ : CM m) : 0 < σ.d := by
  have h := σ.had
  have hm : 0 < (m : ℕ) := m.pos
  rcases Nat.eq_zero_or_pos σ.d with hd | hd
  · rw [hd, Nat.mul_zero] at h; omega
  · exact hd

theorem a_dvd (σ : CM m) : σ.a ∣ (m : ℕ) := ⟨σ.d, σ.had.symm⟩

theorem d_dvd (σ : CM m) : σ.d ∣ (m : ℕ) := ⟨σ.a, by rw [mul_comm]; exact σ.had.symm⟩

theorem a_le (σ : CM m) : σ.a ≤ (m : ℕ) := Nat.le_of_dvd m.pos σ.a_dvd

theorem d_le (σ : CM m) : σ.d ≤ (m : ℕ) := Nat.le_of_dvd m.pos σ.d_dvd

/-- Encode `C(m)` injectively into `Fin (m+1)³` to obtain finiteness. -/
def toFin (σ : CM m) : Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) :=
  (⟨σ.a, by have := σ.a_le; omega⟩,
   ⟨σ.b, by have := σ.hb; have := σ.d_le; omega⟩,
   ⟨σ.d, by have := σ.d_le; omega⟩)

theorem toFin_injective : Function.Injective (toFin (m := m)) := by
  intro x y h
  obtain ⟨xa, xb, xd, _, _, _, _⟩ := x
  obtain ⟨ya, yb, yd, _, _, _, _⟩ := y
  simp only [toFin, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨ha, hb, hd⟩ := h
  subst ha; subst hb; subst hd; rfl

instance : DecidableEq (CM m) := fun x y =>
  decidable_of_iff (x.toFin = y.toFin) toFin_injective.eq_iff

instance : Fintype (CM m) := Fintype.ofInjective toFin toFin_injective

/-- **Cox Lemma 11.11** (skeleton). `C(m)` is in bijection with the right cosets of `Γ₀(m)`.
The witnessing bijection (via `σ ↦ (σ₀⁻¹ SL₂(ℤ) σ) ∩ SL₂(ℤ)`, Cox p. 228) is the
load-bearing leaf for the product reindexing used in (i)/(iv)/(v). -/
theorem nonempty_equiv_rightCosets (m : ℕ+) :
    Nonempty (CM m ≃ Gamma0RightCosets m) := by
  sorry -- T001: Lemma 11.11 bijection via Hermite normal form on coset reps; substantial, left per user policy

/-- Corollary of Lemma 11.11: `|C(m)| = [SL₂(ℤ) : Γ₀(m)]`. -/
theorem card_eq_rightCosets (m : ℕ+) :
    Fintype.card (CM m) = Fintype.card (Gamma0RightCosets m) := by
  obtain ⟨e⟩ := nonempty_equiv_rightCosets m
  exact Fintype.card_congr e

/-- The Möbius action of `σ = (a b; 0 d) ∈ C(m)` on `ℍ`: `στ = (aτ + b)/d`.  Since
`a, d > 0`, this preserves the upper half-plane (`Im(στ) = a·Im(τ)/d > 0`). -/
def cmAction (σ : CM m) (z : ℍ) : ℍ :=
  ⟨((σ.a : ℂ) * (z : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ), by
    have hd : ((σ.d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr σ.d_pos.ne'
    have hz : 0 < (z : ℂ).im := z.2
    have ha : (0 : ℝ) < (σ.a : ℝ) := by exact_mod_cast σ.ha
    have key : (((σ.a : ℂ) * (z : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ)).im
        = (σ.a : ℝ) * (z : ℂ).im / (σ.d : ℝ) := by
      rw [Complex.div_im, Complex.normSq_natCast]
      simp [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
        Complex.natCast_im, Complex.natCast_re]
      field_simp
    rw [key]; positivity⟩

/-- The complex coordinate of `cmAction σ z` is `(aτ + b)/d`. -/
theorem coe_cmAction (σ : CM m) (z : ℍ) :
    ((cmAction σ z : ℍ) : ℂ) = ((σ.a : ℂ) * (z : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ) := rfl

end CM
