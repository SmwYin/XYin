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

theorem DiophantineEquationExample (x y : ℤ) (h : x ^ 3 = y ^ 2 + 1) : x = 1 ∧ y = 0 := by
  -- Every unit of `ℤ[i]` is a cube: the unit group has order `4`, coprime to `3`.
  have unit_cube : ∀ u : GaussianInt, IsUnit u → ∃ c : GaussianInt, c ^ 3 = u := by
    rintro ⟨a, b⟩ hu
    have hn : (⟨a, b⟩ : GaussianInt).norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    have hnorm : (⟨a, b⟩ : GaussianInt).norm = a ^ 2 + b ^ 2 := by simp [Zsqrtd.norm]; ring
    have hnn : (0 : ℤ) ≤ a ^ 2 + b ^ 2 := by positivity
    rw [hnorm] at hn
    have h1 : a ^ 2 + b ^ 2 = 1 := by omega
    have a3 : -1 ≤ a := by nlinarith [sq_nonneg (a + 1), sq_nonneg b]
    have a4 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b]
    have b3 : -1 ≤ b := by nlinarith [sq_nonneg (b + 1), sq_nonneg a]
    have b4 : b ≤ 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg a]
    -- `u⁴ = 1` for every unit `u`, so `u³` is always a cube root of `u`.
    refine ⟨⟨a, b⟩ ^ 3, ?_⟩
    interval_cases a <;> interval_cases b <;> revert h1 <;> decide
  -- Work in `ℤ[i]`, writing `i = ⟨0, 1⟩` and coercing `x`, `y`.
  set i : GaussianInt := ⟨0, 1⟩ with hi
  set X : GaussianInt := (x : GaussianInt) with hX
  set Y : GaussianInt := (y : GaussianInt) with hY
  have hii : i * i = -1 := by rw [hi]; decide
  -- The factorisation `(y + i)(y - i) = x³`.
  have hfact : (Y + i) * (Y - i) = X ^ 3 := by
    have e1 : (Y + i) * (Y - i) = Y ^ 2 + 1 := by linear_combination (-1 : GaussianInt) * hii
    rw [e1, hX, hY]; exact_mod_cast h.symm
  -- `x` is odd: otherwise `y² ≡ -1 (mod 4)`, impossible.
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with ⟨k, hk⟩ | hod
    · exfalso
      have hc : ((x : ZMod 4)) ^ 3 = ((y : ZMod 4)) ^ 2 + 1 := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 4)) h
      rw [hk] at hc
      push_cast at hc
      exact (by decide : ∀ u v : ZMod 4, (u + u) ^ 3 ≠ v ^ 2 + 1) _ _ hc
    · exact hod
  -- Hence `2` and `x³` are coprime in `ℤ`.
  have hcop2 : IsCoprime (2 : ℤ) (x ^ 3) := by
    apply IsCoprime.pow_right
    rw [Int.prime_two.coprime_iff_not_dvd]
    rw [Int.odd_iff] at hxodd
    omega
  -- The factors `y + i` and `y - i` are coprime in `ℤ[i]` (a Bézout combination):
  -- `2 = (-i)(y+i) + i(y-i)` and `x³ = (y+i)(y-i)`, and `gcd(2, x³) = 1`.
  have hcop : IsCoprime (Y + i) (Y - i) := by
    obtain ⟨s, t, hst⟩ := hcop2
    refine ⟨(s : GaussianInt) * (-i) + (t : GaussianInt) * (Y - i), (s : GaussianInt) * i, ?_⟩
    have hst_cast : (s : GaussianInt) * 2 + (t : GaussianInt) * X ^ 3 = 1 := by
      rw [hX]; exact_mod_cast hst
    linear_combination (-2 * (s : GaussianInt)) * hii + (t : GaussianInt) * hfact + hst_cast
  -- Descent: a coprime product equal to a cube makes each factor a cube up to a unit;
  -- absorbing the unit (it is a cube) gives `y + i = (d e)³`.
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop hfact
  obtain ⟨u, hu⟩ := hd
  obtain ⟨e, he0⟩ := unit_cube (↑u) u.isUnit
  have he : Y + i = (d * e) ^ 3 := by rw [mul_pow, he0, hu]
  -- Compare real and imaginary parts of `y + i = (a + b i)³`.
  obtain ⟨a, b, ha, hb⟩ :
      ∃ a b : ℤ, y = a ^ 3 - 3 * a * b ^ 2 ∧ 1 = 3 * a ^ 2 * b - b ^ 3 := by
    set e' := d * e with he'
    refine ⟨e'.re, e'.im, ?_, ?_⟩
    · have hre := congrArg Zsqrtd.re he
      simp [hY, hi, pow_three] at hre
      linear_combination hre
    · have him := congrArg Zsqrtd.im he
      simp [hY, hi, pow_three] at him
      linear_combination him
  -- From `1 = b(3a² - b²)` we get `b = ±1`; `b = 1` is impossible, `b = -1` forces
  -- `a = 0`, hence `y = 0` and `x³ = 1`, i.e. `x = 1`.
  have hbu : IsUnit b := isUnit_of_dvd_one ⟨3 * a ^ 2 - b ^ 2, by linear_combination hb⟩
  rcases Int.isUnit_iff.mp hbu with rfl | rfl
  · exfalso
    have h3 : (3 : ℤ) ∣ 2 := ⟨a ^ 2, by linarith [hb]⟩
    norm_num at h3
  · have ha2 : a ^ 2 = 0 := by linarith [hb]
    have ha0 : a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha2
    subst ha0
    have hy0 : y = 0 := by rw [ha]; ring
    refine ⟨?_, hy0⟩
    have hx3 : x ^ 3 = 1 := by rw [h, hy0]; ring
    exact (Odd.strictMono_pow (by norm_num)).injective hx3
