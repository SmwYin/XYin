import Mathlib

/-!
# A descent example: the Mordell equation `y² = x³ - 1`

The only integer solution of `x³ = y² + 1` is `(x, y) = (1, 0)`.

The proof is the classical descent through the Gaussian integers `ℤ[i]`:
factor `y² + 1 = (y + i)(y - i)` and show the two factors are coprime (this needs
`x` odd, obtained from a reduction modulo `4`). Since `ℤ[i]` is a Bézout domain
their product being a cube forces each factor to be a cube up to a unit, and every
unit of `ℤ[i]` is itself a cube, so `y + i` is a cube `(a + b i)³`. Comparing real
and imaginary parts gives `1 = b(3a² - b²)`, hence `b = ±1`, which pins down
`a = 0`, `b = -1`, and therefore `y = 0`, `x = 1`.
-/

open Zsqrtd

/-- Every unit of the Gaussian integers is a cube: the unit group has order `4`,
coprime to `3`, so `u = (u³)³` for every unit `u`. -/
theorem gaussianInt_isUnit_exists_cube {u : GaussianInt} (hu : IsUnit u) :
    ∃ c : GaussianInt, c ^ 3 = u := by
  obtain ⟨a, b⟩ := u
  have h1 : a ^ 2 + b ^ 2 = 1 := by
    simpa [Zsqrtd.norm, pow_two] using (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr hu
  obtain ⟨a3, a4⟩ := abs_le.mp ((sq_le_one_iff_abs_le_one a).mp (by nlinarith [sq_nonneg b]))
  obtain ⟨b3, b4⟩ := abs_le.mp ((sq_le_one_iff_abs_le_one b).mp (by nlinarith [sq_nonneg a]))
  -- `u⁴ = 1` for every unit `u`, so `u³` is always a cube root of `u`.
  refine ⟨⟨a, b⟩ ^ 3, ?_⟩
  interval_cases a <;> interval_cases b <;> revert h1 <;> decide

/-- In any integer solution of `x³ = y² + 1` the variable `x` is odd: otherwise
`y² ≡ -1 (mod 4)`, which is impossible. -/
private theorem odd_of_pow_three_eq_sq_add_one {x y : ℤ} (h : x ^ 3 = y ^ 2 + 1) :
    Odd x := by
  rcases Int.even_or_odd x with ⟨k, hk⟩ | hod
  · have hc : ((x : ZMod 4)) ^ 3 = ((y : ZMod 4)) ^ 2 + 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 4)) h
    rw [hk] at hc
    push_cast at hc
    exact absurd hc ((by decide : ∀ u v : ZMod 4, (u + u) ^ 3 ≠ v ^ 2 + 1) _ _)
  · exact hod

/-- In `ℤ[i]` the generator `i = sqrtd` squares to `-1`. -/
private theorem gaussianInt_sqrtd_mul_self : (sqrtd * sqrtd : GaussianInt) = -1 := by decide

/-- For `x` odd, the factors of `y² + 1 = (y + i)(y - i)` are coprime in `ℤ[i]`:
`2 = (-i)(y + i) + i(y - i)` is a Bézout combination, and `gcd(2, x³) = 1`. -/
private theorem isCoprime_add_sqrtd_sub_sqrtd {x y : ℤ} (hxodd : Odd x)
    (hfact : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) =
      (x : GaussianInt) ^ 3) :
    IsCoprime ((y : GaussianInt) + sqrtd) ((y : GaussianInt) - sqrtd) := by
  have hcop2 : IsCoprime (2 : ℤ) (x ^ 3) := by
    rw [Int.odd_iff] at hxodd
    exact (Int.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_right
  obtain ⟨s, t, hst⟩ := hcop2
  refine ⟨(s : GaussianInt) * (-sqrtd) + (t : GaussianInt) * ((y : GaussianInt) - sqrtd),
    (s : GaussianInt) * sqrtd, ?_⟩
  have hst_cast : (s : GaussianInt) * 2 + (t : GaussianInt) * (x : GaussianInt) ^ 3 = 1 := by
    exact_mod_cast hst
  linear_combination (-2 * (s : GaussianInt)) * gaussianInt_sqrtd_mul_self +
    (t : GaussianInt) * hfact + hst_cast

/-- Descent core: in any integer solution of `x³ = y² + 1` we have `y = 0`.
Factor over `ℤ[i]`, conclude `y + i = (a + bi)³`, and compare real and imaginary
parts: `1 = b(3a² - b²)` forces `b = -1`, `a = 0`. -/
private theorem eq_zero_of_pow_three_eq_sq_add_one {x y : ℤ} (h : x ^ 3 = y ^ 2 + 1) :
    y = 0 := by
  have hfact : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) =
      (x : GaussianInt) ^ 3 := by
    have e1 : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) =
        (y : GaussianInt) ^ 2 + 1 := by
      linear_combination (-1 : GaussianInt) * gaussianInt_sqrtd_mul_self
    rw [e1]; exact_mod_cast h.symm
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow'
    (isCoprime_add_sqrtd_sub_sqrtd (odd_of_pow_three_eq_sq_add_one h) hfact) hfact
  obtain ⟨e, he0⟩ := gaussianInt_isUnit_exists_cube u.isUnit
  have he : (y : GaussianInt) + sqrtd = (d * e) ^ 3 := by rw [mul_pow, he0, hu]
  -- Compare real and imaginary parts of `y + i = (a + b i)³`.
  obtain ⟨a, b, ha, hb⟩ :
      ∃ a b : ℤ, y = a ^ 3 - 3 * a * b ^ 2 ∧ 1 = 3 * a ^ 2 * b - b ^ 3 := by
    set e' := d * e
    refine ⟨e'.re, e'.im, ?_, ?_⟩
    · have hre := congrArg Zsqrtd.re he
      simp [pow_three] at hre
      linear_combination hre
    · have him := congrArg Zsqrtd.im he
      simp [pow_three] at him
      linear_combination him
  -- `1 = b(3a² - b²)` gives `b = ±1`; `b = 1` is impossible, `b = -1` forces `a = 0`.
  have hbu : IsUnit b := isUnit_of_dvd_one ⟨3 * a ^ 2 - b ^ 2, by linear_combination hb⟩
  rcases Int.isUnit_iff.mp hbu with rfl | rfl
  · exact absurd (⟨a ^ 2, by linarith [hb]⟩ : (3 : ℤ) ∣ 2) (by omega)
  · rw [ha, sq_eq_zero_iff.mp (by linarith [hb] : a ^ 2 = 0)]; ring

theorem DiophantineEquationExample (x y : ℤ) (h : x ^ 3 = y ^ 2 + 1) : x = 1 ∧ y = 0 :=
  have hy : y = 0 := eq_zero_of_pow_three_eq_sq_add_one h
  have hx3 : x ^ 3 = 1 := by rw [h, hy]; ring
  ⟨(Odd.strictMono_pow (by norm_num)).injective hx3, hy⟩
