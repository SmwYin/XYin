/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.LaurentQExpansion.LaurentQExpansion

/-!
# Tests for the Laurent q-expansion coefficient API

Reading off Laurent q-expansion coefficients from a known pole order and a known pole-removed
function.
-/

open UpperHalfPlane

section

variable {h : ℝ} {f g : ℍ → ℂ} {M : ℕ} {n : ℤ}

example (hM : poleOrder h f = M) (hn : n ≥ -(M : ℤ)) :
    (laurentqExpansion h f).coeff n = (toQExpansion h f).coeff (Int.toNat (n + M)) :=
  laurentqExpansion.coeff_of_geq' hM hn

example (hn : n ≥ -(poleOrder h f : ℤ)) (hpr : poleRemoved h f = g) :
    (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + poleOrder h f)) := by
  rw [laurentqExpansion.coeff_of_geq hn, toQExpansion, hpr]

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hn : n ≥ -(1 : ℤ)) :
    (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + 1)) := by
  rw [laurentqExpansion.coeff_of_geq' h1 hn, toQExpansion, hpr, Nat.cast_one]

example (hM : poleOrder h f = M) (hn : n < -(M : ℤ)) :
    (laurentqExpansion h f).coeff n = 0 :=
  laurentqExpansion.coeff_eq_zero_of_lt' hM hn

end

section

variable {h : ℝ} {f g : ℍ → ℂ} {c0 c1 c2 : ℂ}

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g)
    (hcoeff0 : (qExpansion h g).coeff 0 = c0) :
    (laurentqExpansion h f).coeff (-1) = c0 := by
  simpa [toQExpansion, hpr, hcoeff0] using laurentqExpansion.coeff_neg_poleOrder_add' h1 0

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g)
    (hcoeff1 : (qExpansion h g).coeff 1 = c1) :
    (laurentqExpansion h f).coeff 0 = c1 := by
  simpa [toQExpansion, hpr, hcoeff1] using laurentqExpansion.coeff_neg_poleOrder_add' h1 1

example (h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g)
    (hcoeff2 : (qExpansion h g).coeff 2 = c2) :
    (laurentqExpansion h f).coeff 1 = c2 := by
  simpa [toQExpansion, hpr, hcoeff2] using laurentqExpansion.coeff_neg_poleOrder_add' h1 2

end
