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

private theorem gaussianInt_isUnit_exists_cube {u : GaussianInt} (hu : IsUnit u) :
    ∃ c : GaussianInt, c ^ 3 = u := by
  obtain ⟨a, b⟩ := u
  have h1 : a ^ 2 + b ^ 2 = 1 := by
    simpa [Zsqrtd.norm, pow_two] using (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr hu
  obtain ⟨a3, a4⟩ := abs_le.mp ((sq_le_one_iff_abs_le_one a).mp (by nlinarith [sq_nonneg b]))
  obtain ⟨b3, b4⟩ := abs_le.mp ((sq_le_one_iff_abs_le_one b).mp (by nlinarith [sq_nonneg a]))
  refine ⟨⟨a, b⟩ ^ 3, ?_⟩
  interval_cases a <;> interval_cases b <;> revert h1 <;> decide

private theorem odd_of_pow_three_eq_sq_add_one {x y : ℤ} (h : x ^ 3 = y ^ 2 + 1) : Odd x := by
  rw [← Int.not_even_iff_odd]
  rintro ⟨k, rfl⟩
  have hc : ((k : ZMod 4) + k) ^ 3 = (y : ZMod 4) ^ 2 + 1 :=
    mod_cast congrArg (fun z : ℤ ↦ (z : ZMod 4)) h
  exact ((by decide : ∀ u v : ZMod 4, (u + u) ^ 3 ≠ v ^ 2 + 1) _ _) hc

private theorem gaussianInt_sqrtd_mul_self : (sqrtd * sqrtd : GaussianInt) = -1 := rfl

private theorem isCoprime_add_sqrtd_sub_sqrtd {x y : ℤ} (hxodd : Odd x)
    (hfact : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) = (x : GaussianInt) ^ 3) :
    IsCoprime ((y : GaussianInt) + sqrtd) ((y : GaussianInt) - sqrtd) := by
  rw [Int.odd_iff] at hxodd
  obtain ⟨s, t, hst⟩ : IsCoprime (2 : ℤ) (x ^ 3) :=
    (Int.prime_two.coprime_iff_not_dvd.mpr (by lia)).pow_right
  refine ⟨(s : GaussianInt) * (-sqrtd) + (t : GaussianInt) * ((y : GaussianInt) - sqrtd),
    (s : GaussianInt) * sqrtd, ?_⟩
  have hst_cast : (s : GaussianInt) * 2 + (t : GaussianInt) * (x : GaussianInt) ^ 3 = 1 :=
    mod_cast hst
  linear_combination (-2 * (s : GaussianInt)) * gaussianInt_sqrtd_mul_self +
    (t : GaussianInt) * hfact + hst_cast

private theorem eq_zero_of_pow_three_eq_sq_add_one {x y : ℤ} (h : x ^ 3 = y ^ 2 + 1) : y = 0 := by
  have hfact : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) =
      (x : GaussianInt) ^ 3 := by
    have e1 : ((y : GaussianInt) + sqrtd) * ((y : GaussianInt) - sqrtd) =
        (y : GaussianInt) ^ 2 + 1 := by
      linear_combination (-1 : GaussianInt) * gaussianInt_sqrtd_mul_self
    rw [e1]
    exact_mod_cast h.symm
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow'
    (isCoprime_add_sqrtd_sub_sqrtd (odd_of_pow_three_eq_sq_add_one h) hfact) hfact
  obtain ⟨e, he0⟩ := gaussianInt_isUnit_exists_cube u.isUnit
  have he : (y : GaussianInt) + sqrtd = (d * e) ^ 3 := by rw [mul_pow, he0, hu]
  obtain ⟨a, b, ha, hb⟩ :
      ∃ a b : ℤ, y = a ^ 3 - 3 * a * b ^ 2 ∧ 1 = 3 * a ^ 2 * b - b ^ 3 := by
    set e' := d * e
    refine ⟨e'.re, e'.im, ?_, ?_⟩
    · have hre := congrArg Zsqrtd.re he
      simp only [re_add, re_intCast, re_sqrtd, add_zero, pow_three, re_mul, neg_mul,
        one_mul, im_mul] at hre
      linear_combination hre
    · have him := congrArg Zsqrtd.im he
      simp only [im_add, im_intCast, im_sqrtd, zero_add, pow_three, im_mul, re_mul,
        neg_mul, one_mul] at him
      linear_combination him
  have hbu : IsUnit b := isUnit_of_dvd_one ⟨3 * a ^ 2 - b ^ 2, by linear_combination hb⟩
  rcases Int.isUnit_iff.mp hbu with rfl | rfl
  · exact absurd (⟨a ^ 2, by lia⟩ : (3 : ℤ) ∣ 2) (by lia)
  · simp [ha, sq_eq_zero_iff.mp (by lia : a ^ 2 = 0)]

/-- The only integer solution of `x³ = y² + 1` is `(x, y) = (1, 0)`. -/
theorem DiophantineEquationExample (x y : ℤ) (h : x ^ 3 = y ^ 2 + 1) : x = 1 ∧ y = 0 :=
  have hy : y = 0 := eq_zero_of_pow_three_eq_sq_add_one h
  have hx3 : x ^ 3 = 1 := by simp [h, hy]
  ⟨(Odd.strictMono_pow (by norm_num)).injective hx3, hy⟩
