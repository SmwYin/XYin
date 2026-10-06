/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Prime assignments on fractional ideals

Janusz III.3, printed p.103: extend prime values by the finite product of their integer prime
exponents. The target is any commutative group. `primeEvaluation` is the concrete map.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- A prime ideal has its singleton exponent vector. -/
theorem idealExponentVector_primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) :
    idealExponentVector K (primeIdealUnit K v) = Finsupp.single v (1 : ℤ) := by
  classical
  ext w
  rw [idealExponentVector_apply, primeIdealUnit_coe, FractionalIdeal.count_maximal,
    Finsupp.single_apply]

variable {G : Type*} [CommGroup G]

/-- Multiplication of fractional ideals multiplies any assigned prime-power product. -/
theorem primePowerProduct_mul (g : HeightOneSpectrum (𝓞 K) → G)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealExponentVector K (I * J)).prod (fun v n => g v ^ n) =
      (idealExponentVector K I).prod (fun v n => g v ^ n) *
        (idealExponentVector K J).prod (fun v n => g v ^ n) := by
  rw [idealExponentVector_mul]
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

/-- The homomorphism extending an arbitrary prime assignment by integer prime exponents. -/
def primeEvaluation (g : HeightOneSpectrum (𝓞 K) → G) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* G :=
  MonoidHom.mk' (fun I => (idealExponentVector K I).prod (fun v n => g v ^ n))
    (primePowerProduct_mul K g)

/-- The prime-evaluation homomorphism has the specified value on every prime ideal. -/
theorem primeEvaluation_primeIdealUnit (g : HeightOneSpectrum (𝓞 K) → G)
    (v : HeightOneSpectrum (𝓞 K)) : primeEvaluation K g (primeIdealUnit K v) = g v := by
  change (idealExponentVector K (primeIdealUnit K v)).prod (fun w n => g w ^ n) = g v
  rw [idealExponentVector_primeIdealUnit,
    Finsupp.prod_single_index (h := fun w (n : ℤ) => g w ^ n) (zpow_zero _)]
  exact zpow_one _

end Cox.ClassFieldTheory
