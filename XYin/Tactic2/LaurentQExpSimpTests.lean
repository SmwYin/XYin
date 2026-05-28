import XYin.LaurentQExpansion.LaurentQExpansion

open UpperHalfPlane

section

variable {h : ℝ} {f g : ℍ → ℂ} {M : ℕ} {n : ℤ}

example (hM : poleOrder h f = M) (hn : n ≥ -(M : ℤ)) :
    (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + M)) := by
  have hn' : n ≥ -(poleOrder h f : ℤ) := by
    simpa [hM] using hn
  simpa [hM] using
    (laurentqExpansion.coeff_of_geq (h := h) (f := f) (n := n) hn')

example (hn : n ≥ -(poleOrder h f : ℤ)) (hpr : poleRemoved h f = g) :
    (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + poleOrder h f)) := by
  simpa [to_qExpansion, hpr] using
    (laurentqExpansion.coeff_of_geq (h := h) (f := f) (n := n) hn)

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hn : n ≥ -(1 : ℤ)) :
    (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + 1)) := by
  have hn' : n ≥ -(poleOrder h f : ℤ) := by
    simpa [h1] using hn
  simpa [to_qExpansion, h1, hpr] using
    (laurentqExpansion.coeff_of_geq (h := h) (f := f) (n := n) hn')

example (hM : poleOrder h f = M) (hn : n < -(M : ℤ)) :
    (laurentqExpansion h f).coeff n = 0 := by
  have hn' : n < -(poleOrder h f : ℤ) := by
    simpa [hM] using hn
  simpa using
    (laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) (n := n) hn')

example (hM : poleOrder h f = M) (hn : n < -(M : ℤ)) :
    (laurentqExpansion h f).coeff n = 0 := by
  have hn' : n < -(poleOrder h f : ℤ) := by
    simpa [hM] using hn
  simpa using
    (laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) (n := n) hn')

end

section

variable {h : ℝ} {f g : ℍ → ℂ} {c0 c1 c2 : ℂ}

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff0 : (qExpansion h g).coeff 0 = c0) :
    (laurentqExpansion h f).coeff (-1) = c0 := by
  simpa [to_qExpansion, h1, hpr, hcoeff0] using
    (laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) 0)

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff1 : (qExpansion h g).coeff 1 = c1) :
    (laurentqExpansion h f).coeff 0 = c1 := by
  simpa [to_qExpansion, h1, hpr, hcoeff1] using
    (laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) 1)

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff2 : (qExpansion h g).coeff 2 = c2) :
    (laurentqExpansion h f).coeff 1 = c2 := by
  simpa [to_qExpansion, h1, hpr, hcoeff2] using
    (laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) 2)

end
