/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Arithmetic

/-!
# Planning skeleton: the polynomial step in Cox Theorem 11.1

This unproved statement isolates the final algebraic step of Cox's integrality argument.
The book's primitive-element and proper-ideal lattice arguments remain separate obligations.
-/

namespace Cox

/-- Cox, proof of Theorem 11.1, p. 237: a nonsquare diagonal root is integral. -/
theorem isIntegral_of_modularPolynomialDiagonal_root {R : Type*} [CommRing R]
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) {x : R}
    (hx : (modularPolynomialDiagonal m).eval₂ (Int.castRingHom R) x = 0) :
    IsIntegral ℤ x := by
  sorry

end Cox
