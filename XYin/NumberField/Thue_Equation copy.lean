import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Xiangmiao (Samuel) Yin

-- The only solutions in integers of the Thue equation x³-2y³=1 are (1,0) and (-1,-1).

-- Section 1: Foundation

-- 1.1 The ring

@[ext]
structure R where
  x : ℤ
  y : ℤ
  z : ℤ

@[simp]
def α : R := ⟨0,1,0⟩

namespace R

def one : R := ⟨1,0,0⟩
def zero : R := ⟨0,0,0⟩
def add (a b : R) : R := ⟨a.x+b.x, a.y+b.y, a.z + b.z⟩
def neg (a : R) : R := ⟨-a.x,-a.y,-a.z⟩
def mul (a b : R) : R where
  x := a.x * b.x + 2* a.y * b.z + 2* a.z * b.y
  y := a.x * b.y + a.y * b.x + 2 * a.z * b.z
  z := a.x * b.z + a.y * b.y + a.z * b.x

instance : One R := ⟨one⟩
instance : Zero R := ⟨zero⟩
instance : Add R := ⟨add⟩
instance : Neg R := ⟨neg⟩
instance : Mul R := ⟨mul⟩

variable (a b c : R)

lemma one_def : (1 : R) = ⟨1,0,0⟩ := rfl

lemma zero_def : (0 : R) = ⟨0,0,0⟩ := rfl

lemma add_def : a + b = ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩ := rfl

lemma neg_def : - a = ⟨-a.x, -a.y, -a.z⟩ := rfl

lemma mul_def : a * b = {
    x := a.x * b.x + 2* a.y * b.z + 2* a.z * b.y
    y := a.x * b.y + a.y * b.x + 2 * a.z * b.z
    z := a.x * b.z + a.y * b.y + a.z * b.x } := rfl

lemma add_assoc : a + b + c = a + (b + c) := by
  ext <;> simp only [add_def] <;> ring

lemma zero_add : 0 + a = a := by
  ext <;> simp only [add_def, zero_def] <;> ring

lemma add_zero : a + 0 = a := by
  ext <;> simp only [add_def, zero_def] <;> ring

lemma add_comm : a + b = b + a := by
  ext <;> simp only [add_def] <;> ring

lemma left_distrib : a * (b + c) = a * b + a * c := by
  ext <;> simp only [add_def, mul_def] <;> ring

lemma right_distrib : (a + b) * c = a * c + b * c := by
  ext <;> simp only [add_def, mul_def] <;> ring

lemma zero_mul : 0 * a = 0 := by
  ext <;> simp only [zero_def, mul_def] <;> ring

lemma mul_zero : a * 0 = 0 := by
  ext <;> simp only [zero_def, mul_def] <;> ring

lemma one_mul : 1 * a = a := by
  ext <;> simp only [one_def, mul_def] <;> ring

lemma mul_one : a * 1 = a := by
  ext <;> simp only [one_def, mul_def] <;> ring

lemma mul_assoc : a * b * c = a * (b * c) := by
  ext <;> simp only [mul_def] <;> ring

lemma mul_comm : a * b = b * a := by
  ext <;> simp only [mul_def] <;> ring

lemma add_left_neg : -a + a = 0 := by
  ext <;> simp only [neg_def, add_def, zero_def] <;> ring

instance : CommRing R where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := add_left_neg

-- 1.2 Quantitative lemmas

@[simp]
lemma int_cast_r (x : ℤ) : (↑x : R) = ⟨x, 0, 0⟩ := by
  induction x using Int.induction_on with
  | zero => rfl
  | succ n ih =>
    rw [Int.cast_add, Int.cast_one, ih]
    rfl
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, ih]
    rfl

lemma z_coord_int_add_int_mul_alpha_add_int_mul_alpha_sq (x : ℤ) (y : ℤ) (z : ℤ) :
    (x + y * α + z * α ^ 2).z = z := by
  simp only [add_def, sq, mul_def, α, int_cast_r]; ring

lemma z_coord_int_add_alpha_mul_int_add_alpha_sq_mul_int (x : ℤ) (y : ℤ) (z : ℤ) :
    (x + α * y + α ^ 2 * z).z = z := by
  simp only [add_def, sq, mul_def, α, int_cast_r]; ring

-- 1.3 R in ℝ

-- 1.3.1 Key elements

noncomputable section
macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

@[simp]
def α₁ : ℝ := (2: ℝ) ^ (1/3 : ℝ)

@[simps]
def ω : ℂ := ⟨-1/2 , Real.sqrt 3 / 2⟩

@[simp]
def α₂ : ℂ := α₁ * ω

@[simp]
def α₃ : ℂ := α₁ * (- ω - 1)

-- 1.3.2 Quantitative lemmas

notation "√3" => Real.sqrt 3

lemma sqrt_three_sq : √3^2 = 3 := by norm_num

lemma one_lt_one_add_alpha₁_add_alpha₁_sq : (1 : ℝ) < (1 : ℝ) + α₁ + α₁ ^ 2 := by
  nlinarith [show (0 : ℝ) < α₁ from Real.rpow_pos_of_pos two_pos (1 / 3 : ℝ)]

lemma one_lt_alpha₁ : 1 < α₁ := by norm_num [α₁, Real.one_lt_rpow_iff zero_le_two]

lemma one_lt_alpha₁_sq : (1 : ℝ) < α₁ ^ 2 := by nlinarith [one_lt_alpha₁]

@[simp]
lemma alpha₁_pow_three : α₁ ^ 3 = 2 := by
  simpa [α₁, one_div] using
    (Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3) zero_le_two (by norm_num))

@[simp]
lemma alpha₁_pow_four : α₁ ^ 4  = 2 * α₁ := by
  rw [show α₁ ^ 4 = α₁ * α₁ ^ 3 by ring, alpha₁_pow_three]; ring

lemma omega_conjugate : star ω = - ω - 1 := by
  apply Complex.ext <;> norm_num [ω]

@[simp]
lemma omega_sq : ω ^ 2 = -ω - 1 := by
  simp only [pow_two]
  apply Complex.ext <;> norm_num [ω, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt_three_sq]

@[simp]
lemma omega_pow_three : ω ^ 3 = 1 := by
  rw [show ω ^ 3 = ω * ω ^ 2 by ring, omega_sq]; ring_nf; simp [omega_sq]

lemma norm_omega_eq_one : ‖ω‖ = (1 : ℝ) := by
  norm_num [Complex.norm_def, Complex.normSq_apply, ω]; nlinarith [sqrt_three_sq]

lemma norm_neg_omega_sub_one_eq_one : ‖-ω - 1‖ = (1 : ℝ) := by
  simp [← omega_sq, norm_omega_eq_one]

-- 1.4 Ring homomorphism

@[simp]
def σ₁ : R →+* ℝ where
  toFun a   := a.x + a.y * α₁ + a.z * α₁ ^ 2
  map_one'  := by simp [one_def]
  map_mul'  := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]; ring_nf
    simp only [alpha₁_pow_three, alpha₁_pow_four]; ring_nf
  map_zero' := by simp [zero_def]
  map_add'  := by intro x y; simp only [add_def, Int.cast_add]; ring

@[simp]
def σ₂ : R →+* ℂ where
  toFun a := a.x + a.y * α₂ + a.z * α₂ ^ 2
  map_one' := by simp [one_def]
  map_mul' := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]; ring_nf
    have hα₂3 : α₂ ^ 3 = 2 := by
      rw [α₂]
      ring_nf
      simpa [omega_pow_three] using congrArg (fun t : ℝ => (t : ℂ)) alpha₁_pow_three
    have hα₂4 : α₂ ^ 4 = 2 * α₂ := by
      rw [show α₂ ^ 4 = α₂ * α₂ ^ 3 by ring, hα₂3]; ring
    simp only [hα₂3, hα₂4]; ring_nf
  map_zero' := by simp [zero_def]
  map_add' := by intro x y; simp only [add_def, Int.cast_add]; ring

@[simp]
def σ₃ : R →+* ℂ where
  toFun a := a.x + a.y * α₃ + a.z * α₃ ^ 2
  map_one' := by simp [one_def]
  map_mul' := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]; ring_nf
    have hα₃3 : α₃ ^ 3 = 2 := by
      rw [α₃, ← omega_sq]
      ring_nf
      norm_cast
      have hω6 : ω ^ 6 = 1 := by
        simpa [omega_pow_three] using show ω ^ 6 = (ω ^ 3) ^ 2 by ring
      simpa [hω6] using congrArg (fun t : ℝ => (t : ℂ)) alpha₁_pow_three
    have hα₃4 : α₃ ^ 4 = 2 * α₃ := by
      rw [show α₃ ^ 4 = α₃ * α₃ ^ 3 by ring, hα₃3]; ring
    simp only [hα₃3, hα₃4]; ring_nf
  map_zero' := by simp [zero_def]
  map_add' := by intro x y; simp only [add_def, Int.cast_add]; ring

lemma pow_sigma_eq_sigma_pow (u : Rˣ) (n : ℤ) : σ₁ u ^ n = σ₁ (u ^ n) := by
  cases n <;> simp [σ₁, Int.ofNat_eq_natCast, zpow_natCast, zpow_negSucc, map_units_inv,
    Units.val_pow_eq_pow_val, map_pow]

lemma sigma_conjugate : σ₃ a = star (σ₂ a) := by
  apply Complex.ext <;> simp [σ₃, σ₂, α₃, α₂, omega_conjugate]

lemma norm_sigma_two_eq_norm_sigma_three : ‖σ₂ a‖ = ‖σ₃ a‖ := by
  rw [sigma_conjugate]
  simpa using (Complex.norm_conj (σ₂ a)).symm

lemma sigma_two_mul_sigma_three_eq_norm_sigma_two_sq :
    σ₂ a * σ₃ a = ((‖σ₂ a‖) ^ 2 : ℝ) := by
  rw [sigma_conjugate]
  simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (σ₂ a)

-- 1.5 Norm

@[simp]
def norm : R →* ℤ where
  toFun a := a.x^3 + 2*a.y^3 + 4*a.z^3 - 6*a.x*a.y*a.z
  map_one' := by rfl
  map_mul' := by intro x y; simp only [mul_def, Nat.cast_ofNat]; ring

lemma norm_eq_sigma_one_mul_sigma_two_mul_sigma_three : norm a = σ₁ a * σ₂ a * σ₃ a := by
  simp only [
    norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub, Int.cast_add,
    Int.cast_pow, Int.cast_mul, σ₁, RingHom.coe_mk, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, σ₂, σ₃, α₂, α₃
  ]
  ring_nf
  norm_cast
  have hα6 : α₁ ^ 6 = 4 := by
    rw [show α₁ ^ 6 = α₁ ^ 3 * α₁ ^ 3 by ring, alpha₁_pow_three]
    norm_num
  have hω4 : ω ^ 4 = ω := by rw [show ω ^ 4 = ω * ω ^ 3 by ring, omega_pow_three]; ring
  simp only [alpha₁_pow_three, alpha₁_pow_four, hα6, hω4, omega_pow_three]
  ring_nf
  norm_num; ring

lemma norm_eq_sigma_one_mul_norm_sigma_two_sq : norm a = σ₁ a * ‖σ₂ a‖ ^ 2 := by
  have h := norm_eq_sigma_one_mul_sigma_two_mul_sigma_three a
  rw [_root_.mul_assoc, sigma_two_mul_sigma_three_eq_norm_sigma_two_sq a] at h; norm_cast at h

-- 1.6 Units

-- 1.6.1 General properties

lemma unit_of_norm (h : norm a = 1) : ∃ u : Rˣ, u = a := by
  refine ⟨Units.mkOfMulEqOne a
    ⟨a.x ^ 2 - 2 * a.y * a.z, 2 * a.z ^ 2 - a.x * a.y, a.y ^ 2 - a.x * a.z⟩ ?_, rfl⟩
  ext <;> simp only [Nat.cast_ofNat, mul_def, one_def]
  · rw [← h]
    simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk]; ring
  all_goals ring

lemma sigma_norm_one_pos (h : norm a = 1) : 0 < σ₁ a := by
  by_contra! nh
  have nA : (norm a : ℝ) ≤ 0 := by
    rw [norm_eq_sigma_one_mul_norm_sigma_two_sq]
    exact mul_nonpos_of_nonpos_of_nonneg nh (sq_nonneg ‖σ₂ a‖)
  rw [Int.cast_nonpos] at nA; lia

lemma sigma_unit_neq_zero (u : Rˣ) : σ₁ u.val ≠ 0 :=
  left_ne_zero_of_mul_eq_one (by
    rw [← RingHom.map_mul, u.val_inv, RingHom.map_one])

lemma abs_sigma_unit_pos (u : Rˣ) : 0 < |σ₁ u.val| := abs_pos.mpr (sigma_unit_neq_zero u)

-- 1.6.2 The fundamental unit

@[simp]
def fund : Rˣ where
  val := 1 + α + α^2
  inv := α - 1
  val_inv := by simp only [Nat.cast_one, α]; ring_nf; rfl
  inv_val := by simp only [α, Nat.cast_one]; ring_nf; rfl

lemma fund_inv : fund ^ (-1:ℤ) = -1 + α := by
  simp only [fund, Nat.cast_one, α, zpow_neg, zpow_one, Units.inv_mk]; ring

lemma norm_fund : norm fund = 1 := rfl

lemma norm_fund_inv : norm (fund⁻¹:Rˣ) = 1 := rfl

lemma norm_fund_pow (n : ℤ) : norm (fund ^ n) = 1 := by
  cases n with
  | ofNat n =>
    change norm ((fund : R) ^ n) = 1
    rw [map_pow norm (fund : R) n, norm_fund]; norm_num
  | negSucc n =>
    change norm (((fund⁻¹ : Rˣ) : R) ^ (n + 1)) = 1
    rw [map_pow norm ((fund⁻¹ : Rˣ) : R) (n + 1), norm_fund_inv]; norm_num

lemma fund_mul_pow (n : ℤ) : fund * fund ^ n = fund ^ (n + 1) := by
  simpa [Int.add_comm] using (zpow_add fund 1 n).symm

lemma sigma_fund_pos : 0 < σ₁ fund :=
  lt_trans zero_lt_one (by
    simpa [σ₁, fund, α, one_def, add_def, mul_def, pow_two] using
      one_lt_one_add_alpha₁_add_alpha₁_sq)

lemma sigma_fund_inv (n : ℤ) : 0 < σ₁ (fund ^ n) := by
  rw [← pow_sigma_eq_sigma_pow (u := fund) (n := n)]; exact zpow_pos sigma_fund_pos n

lemma fund_pow_sub (n : ℤ) : fund ^ (n + 1) * fund ^ (-n) = fund := by
  simpa using (zpow_add fund (n + 1) (-n)).symm


-- Section 2: Every element of ℤ[α] with norm 1 is a power of fund

-- 2.1 Finding the exponent with log

noncomputable def ℓ : Rˣ → ℝ := fun u ↦ Real.log |σ₁ u.val|

lemma ell_fund_pos : ℓ fund > 0 := by
  apply Real.log_pos; rw [abs_of_pos sigma_fund_pos]
  simpa [fund, α, σ₁, one_def, add_def, mul_def, pow_two] using
    one_lt_one_add_alpha₁_add_alpha₁_sq

lemma exists_sigma_one_between_fund_zpows_of_norm_eq_one (u : Rˣ) (h : norm u = 1) :
    ∃ n : ℤ, σ₁ (fund ^ n) ≤ σ₁ u ∧ σ₁ u < σ₁ (fund ^ (n + 1)) := by
  let n:= Int.floor (ℓ u / ℓ fund)
  use n
  have hle1: n ≤ ℓ u / ℓ fund := Int.floor_le (ℓ u / ℓ fund)
  have hl1: ℓ u / ℓ fund < n + 1 := Int.lt_floor_add_one (ℓ u / ℓ fund)
  have h': 0 < ℓ fund := ell_fund_pos
  have hle2: n * ℓ fund ≤ ℓ u := by
    simpa only [div_mul, div_self h'.ne', div_one] using mul_le_mul_of_nonneg_right hle1 h'.le
  have hl2: ℓ u < (n + 1) * ℓ fund := by
    simpa only [div_mul, div_self h'.ne', div_one] using mul_lt_mul_of_pos_right hl1 h'
  have he1: n * ℓ fund = Real.log (|σ₁ fund.val|^n) := by rw [ℓ, Real.log_zpow]
  have he2: (n + 1) * ℓ fund = Real.log (|σ₁ fund.val|^(n+1)) := by
    rw [ℓ, Real.log_zpow]; norm_cast
  rw [he1, ℓ] at hle2; rw [he2, ℓ] at hl2
  have h01: 0 < |σ₁ fund.val| := abs_sigma_unit_pos fund
  have h01': 0 < |σ₁ fund.val| ^ n := zpow_pos h01 n
  have h02: 0 < |σ₁ u.val| := abs_sigma_unit_pos u
  have h02': 0 < |σ₁ fund.val| ^ (n + 1) := zpow_pos h01 (n + 1)
  have hle3: |σ₁ fund.val| ^ n ≤ |σ₁ u.val| := by
    rwa [Real.log_le_log_iff h01' h02] at hle2
  have hl3: |σ₁ u.val| < |σ₁ fund.val| ^ (n + 1) := by
    rwa [Real.log_lt_log_iff h02 h02'] at hl2
  have hle3': (σ₁ fund.val) ^ n ≤ σ₁ u.val := by
    rwa [← abs_of_pos sigma_fund_pos, ← abs_of_pos (sigma_norm_one_pos u h)]
  have hl3': σ₁ u.val < (σ₁ fund.val) ^ (n + 1) := by
    rwa [← abs_of_pos sigma_fund_pos, ← abs_of_pos (sigma_norm_one_pos u h)]
  rw [pow_sigma_eq_sigma_pow] at hle3' hl3'
  exact ⟨hle3', hl3'⟩

-- 2.2  Bound on σ₁ fund

lemma alpha₁_lt_13_div_10 : (2 : ℝ) ^ ((1 / 3) : ℝ) < 13 / 10 := by
  rw [one_div, Real.rpow_inv_lt_iff_of_pos zero_le_two (by norm_num) zero_lt_three]; norm_num

lemma sigma_fund_bound : σ₁ fund < 4 := by
  simp only [fund, α, σ₁, α₁, Nat.cast_one, map_add, map_one, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_zero, Int.cast_one, _root_.one_mul,
    _root_.zero_add, MulZeroClass.zero_mul, _root_.add_zero, map_pow]
  nlinarith [alpha₁_lt_13_div_10, Real.rpow_pos_of_pos two_pos ((1 : ℝ) / 3)]

-- 2.3 Bounds on coefficients

-- 2.3.1 Solving linear system

lemma abs_three_x_sub_sigma_one_eq_norm_sigma_two_add_sigma_three :
    |3 * a.x - σ₁ a| = ‖σ₂ a + σ₃ a‖ := by
  calc
  _ = ‖(3 * a.x - σ₁ a : ℂ)‖ := by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (3 * a.x - σ₁ a)).symm
  _ = _ := by
    congr
    simp only [
      σ₁, α₁, one_div, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_pow,
      σ₂, α₂, σ₃, α₃
    ]
    ring_nf
    simp only [omega_sq]
    ring_nf

lemma abs_three_alpha₁_y_sub_sigma_one_eq_norm_sigma_y_sum :
    |3 * α₁ * a.y - σ₁ a| = ‖(-ω - 1) * σ₂ a + ω * σ₃ a‖ := by
  calc
  _ = ‖(3 * α₁ * a.y - σ₁ a : ℂ)‖ := by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (3 * α₁ * a.y - σ₁ a)).symm
  _ = _ := by
    congr
    simp only [
      α₁, one_div, σ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_pow,
      σ₂, α₂, σ₃, α₃
    ]
    ring_nf
    simp only [omega_sq]
    ring_nf

lemma abs_three_alpha₁_sq_z_sub_sigma_one_eq_norm_sigma_z_sum :
    |3 * α₁^2 * a.z - σ₁ a| = ‖ω * σ₂ a + (-ω - 1) * σ₃ a‖ := by
  calc
  _ = ‖(3 * α₁ ^ 2 * a.z - σ₁ a : ℂ)‖ := by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (3 * α₁ ^ 2 * a.z - σ₁ a)).symm
  _ = _ := by
    congr
    simp only [
      Nat.cast_ofNat, α₁, one_div, Complex.ofReal_pow, σ₁, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, Complex.ofReal_add, Complex.ofReal_intCast,
      Complex.ofReal_mul, σ₂, α₂, σ₃, α₃
    ]
    ring_nf
    simp only [omega_sq]
    ring_nf

-- 2.3.2 Derivation of the bounds

lemma lt_two_of_three_mul_sub_le_two_of_lt_four (x : ℝ) (y : ℝ) (h1 : y < 4)
    (h2 : 3 * x - y ≤ 2) : x < 2 := by
  nlinarith

lemma neg_inv_three_le_of_sub_le_two_of_one_le (x : ℝ) (y : ℝ) (h1 : 1 ≤ y)
    (h2 : y - 3 * x ≤ 2) : -3⁻¹ ≤ x := by
  nlinarith

lemma lt_two_of_mul_lt_two_of_one_lt (x : ℝ) (y : ℝ) (h1 : 1 < y) (h2 : y * x < 2) : x < 2 := by
  nlinarith

lemma int_lt_two_iff_le_one (x : ℤ) : x < (2 : ℝ) ↔ x ≤ 1 := by
  exact_mod_cast (by lia : x < (2 : ℤ) ↔ x ≤ 1)

lemma neg_inv_three_lt_of_neg_inv_three_le_mul_of_one_lt (x : ℝ) (y : ℝ)
    (h1 : 1 < y) (h2 : -3⁻¹ ≤ y * x) : -3⁻¹ < x := by
  by_contra! nh
  nlinarith [mul_lt_mul_of_neg_right h1 (by nlinarith : x < 0)]

lemma neg_inv_three_le_int_cast_iff_nonneg (x : ℤ) : -3⁻¹ ≤ (x : ℝ) ↔ 0 ≤ x := by
  constructor <;> intro h
  · by_contra! hx
    nlinarith [(Int.cast_le_neg_one_of_neg hx : (x : ℝ) ≤ -1)]
  · nlinarith [show (0 : ℝ) ≤ x by exact_mod_cast h]

lemma neg_inv_three_lt_int_cast_iff_nonneg (x : ℤ) : -3⁻¹ < (x : ℝ) ↔ 0 ≤ x :=
  ⟨fun h => (neg_inv_three_le_int_cast_iff_nonneg x).mp h.le, fun h => by
    nlinarith [show (0 : ℝ) ≤ x by exact_mod_cast h]⟩

lemma eq_zero_or_eq_one_of_le_one_of_nonneg (x : ℤ) (h1 : x ≤ 1) (h2 : 0 ≤ x) :
    x = 0 ∨ x = 1 := by
  lia

-- 2.3.3 Checking possible values

lemma unit_eq_one_or_fund_of_coeffs_zero_or_one (A : Rˣ) (h : norm A = 1)
    (h1 : (A : R).x = 0 ∨ (A : R).x = 1)
    (h2 : (A : R).y = 0 ∨ (A : R).y = 1)
    (h3 : (A : R).z = 0 ∨ (A : R).z = 1) :
    A = (1 : Rˣ) ∨ A = fund := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    aesop (add norm_num [norm])

-- 2.4 The theorem

theorem unit_eq_fund_pow (u : Rˣ) (h : norm u = 1) : ∃ n : ℤ, u = fund ^ n := by
  obtain ⟨n, hn1, hn2⟩:= exists_sigma_one_between_fund_zpows_of_norm_eq_one u h
  let A:= u * fund ^ (-n)
  have hnormA: norm A = 1 := by
    calc
    _ = norm u * norm (fund ^ (-n)) := MonoidHom.map_mul norm u (fund ^ (-n))
    _ = 1 := by rw [h, norm_fund_pow]; norm_num
  have h': 0 < σ₁ (fund ^ (-n)) := sigma_fund_inv (-n)
  have hA1: (1:ℝ) ≤ σ₁ A := by
    calc
    _ = σ₁ 1 := (RingHom.map_one σ₁).symm
    _ = σ₁ (fund ^ n * fund ^ (-n)) := by
      congr
      simp only [fund, Nat.cast_one, α, zpow_neg, Units.mul_inv]
    _ = σ₁ (fund ^ n) * σ₁ (fund ^ (-n)) := RingHom.map_mul σ₁ (fund ^ n) (fund ^ (-n))
    _ ≤ σ₁ u * σ₁ (fund ^ (-n)) := mul_le_mul_of_nonneg_right hn1 h'.le
    _ = _ := (RingHom.map_mul σ₁ u (fund ^ (-n))).symm
  have hApos: 0 < σ₁ A := sigma_norm_one_pos A hnormA
  have hA2: σ₁ A < σ₁ fund := by
    calc
    _ = σ₁ u * σ₁ (fund ^ (-n)) := RingHom.map_mul σ₁ ↑u ↑(fund ^ (-n))
    _ < σ₁ (fund ^ (n + 1)) * σ₁ (fund ^ (-n)) := mul_lt_mul_of_pos_right hn2 h'
    _ = σ₁ fund := by
      simpa [RingHom.map_mul] using congrArg (fun t : Rˣ => σ₁ (t : R)) (fund_pow_sub n)
  have hσ₂A : ‖σ₂ A‖ ≤ 1 := by
    by_contra! hσ₂A
    have nhnormA : (1 : ℤ) < norm A := by
      exact_mod_cast (show (1 : ℝ) < (norm A : ℝ) by
        rw [norm_eq_sigma_one_mul_norm_sigma_two_sq A]
        nlinarith [hσ₂A, hA1, hApos])
    lia
  have norm_sum_le_two (c d : ℂ) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
      ‖c * σ₂ A + d * σ₃ A‖ ≤ 2 := by
    have htri := norm_add_le (c * σ₂ A) (d * σ₃ A)
    rw [Complex.norm_mul, Complex.norm_mul, hc, hd, ← norm_sigma_two_eq_norm_sigma_three]
      at htri
    nlinarith [hσ₂A, htri]
  have A.x_bound: |3 * (A:R).x - σ₁ A| ≤ 2 := by
    rw [abs_three_x_sub_sigma_one_eq_norm_sigma_two_add_sigma_three A]
    simpa using norm_sum_le_two 1 1 (by norm_num) (by norm_num)
  have A.y_bound: |3 * α₁ * (A:R).y - σ₁ A| ≤ 2 := by
    rw [abs_three_alpha₁_y_sub_sigma_one_eq_norm_sigma_y_sum A]
    exact norm_sum_le_two (-ω - 1) ω norm_neg_omega_sub_one_eq_one norm_omega_eq_one
  have A.z_bound: |(3:ℝ) * α₁^2 * (A:R).z - σ₁ A| ≤ 2 :=
    (abs_three_alpha₁_sq_z_sub_sigma_one_eq_norm_sigma_z_sum A).trans_le <|
      norm_sum_le_two ω (-ω - 1) norm_omega_eq_one norm_neg_omega_sub_one_eq_one
  rw [abs_sub_le_iff] at A.x_bound A.y_bound A.z_bound
  obtain ⟨A.x1, A.x2⟩ := A.x_bound
  obtain ⟨A.y1, A.y2⟩ := A.y_bound
  obtain ⟨A.z1, A.z2⟩ := A.z_bound
  have hAb: σ₁ A < 4 := lt_trans hA2 sigma_fund_bound
  have scaled_value (v : ℤ) (c : ℝ) (hc : 1 < c) (hupper : c * v < 2)
      (hlower : -3⁻¹ ≤ c * v) : v = 0 ∨ v = 1 := by
    have hle := lt_two_of_mul_lt_two_of_one_lt v c hc hupper
    rw [int_lt_two_iff_le_one v] at hle
    have hnonneg := neg_inv_three_lt_of_neg_inv_three_le_mul_of_one_lt v c hc hlower
    rw [neg_inv_three_lt_int_cast_iff_nonneg v] at hnonneg
    exact eq_zero_or_eq_one_of_le_one_of_nonneg v hle hnonneg
  have A.x11 := lt_two_of_three_mul_sub_le_two_of_lt_four (A:R).x (σ₁ A) hAb A.x1
  rw [_root_.mul_assoc] at A.y1 A.z1 A.y2 A.z2
  have A.y11 := lt_two_of_three_mul_sub_le_two_of_lt_four (α₁ * (A:R).y) (σ₁ A) hAb A.y1
  have A.z11 := lt_two_of_three_mul_sub_le_two_of_lt_four (α₁ ^ 2 * (A:R).z) (σ₁ A) hAb A.z1
  have A.x21 := neg_inv_three_le_of_sub_le_two_of_one_le (A:R).x (σ₁ A) hA1 A.x2
  have A.y21 := neg_inv_three_le_of_sub_le_two_of_one_le (α₁ * (A:R).y) (σ₁ A) hA1 A.y2
  have A.z21 := neg_inv_three_le_of_sub_le_two_of_one_le (α₁ ^ 2 * (A:R).z) (σ₁ A) hA1 A.z2
  rw[int_lt_two_iff_le_one (A:R).x] at A.x11
  rw[neg_inv_three_le_int_cast_iff_nonneg (A:R).x] at A.x21
  have A.x_value := eq_zero_or_eq_one_of_le_one_of_nonneg (A:R).x A.x11 A.x21
  have A.y_value := scaled_value (A:R).y α₁ one_lt_alpha₁ A.y11 A.y21
  have A.z_value := scaled_value (A:R).z (α₁^2) one_lt_alpha₁_sq A.z11 A.z21
  rcases unit_eq_one_or_fund_of_coeffs_zero_or_one A hnormA A.x_value A.y_value
      A.z_value with h1 | h2
  · exact ⟨n, by rw [show u = A * fund ^ n by simp [A], h1, _root_.one_mul]⟩
  · exact ⟨n+1, by rw [show u = A * fund ^ n by simp [A], h2, fund_mul_pow]⟩


-- Section 3: Tricks with mod

-- 3.2 If fundⁿ = x-yα then n is congruent to 0 or -1 mod 3

lemma fund_zpow_three_nat_eq_one_add_three_mul (n : ℕ) :
    ∃ k : R, fund ^ (3 * n : ℤ) = 1 + 3 * k := by
  induction n with
  | zero => use 0; simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨v, hv⟩ : ∃ k : R, fund ^ (3 : ℤ) = 3 * k + 1 := by
      refine ⟨⟨6, 5, 4⟩, ?_⟩
      simp only [fund, Nat.cast_one, α]; ext <;> (ring_nf; rfl)
    use k + v + 3 * k * v
    push_cast; rw [mul_add, Int.mul_one, zpow_add]
    push_cast; rw [hk, hv]; ring

lemma fund_zpow_neg_three_nat_eq_one_add_three_mul (n : ℕ) :
    ∃ k : R, (fund ^ (- (3 * n):ℤ)) = 1 + 3 * k := by
  induction n with
  | zero => use 0; simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨v, hv⟩ : ∃ k : R, fund ^ (-3 : ℤ) = 3 * k + 1 := by
      refine ⟨⟨0, 1, -1⟩, ?_⟩
      simp only [fund, Nat.cast_one, α]; ext <;> (ring_nf; rfl)
    use k + v + 3 * k * v
    push_cast; rw [mul_add, Int.mul_one, neg_add, zpow_add]
    push_cast; rw [hk, hv]; ring

lemma fund_zpow_three_int_eq_one_add_three_mul (n : ℤ) :
    ∃ k : R, fund ^ (3 * n) = 1 + 3 * k := by
  cases n with
  | ofNat n =>
    exact fund_zpow_three_nat_eq_one_add_three_mul n
  | negSucc n =>
    rw [Int.negSucc_eq]; exact_mod_cast fund_zpow_neg_three_nat_eq_one_add_three_mul (n+1)

lemma one_add_three_mul_mul_fund_eq_expansion (v : R) :
    ((1 : R) + (3 : R) * v) * fund =
      ((1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z) +
      α * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z) +
      α ^ 2 * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z) := by
  have three : (3 : R) = ⟨3, 0, 0⟩ := by simpa using (int_cast_r 3)
  have h : (1 : R) + (3 : R) * v = ⟨1 + 3 * v.x, 3 * v.y, 3 * v.z⟩ := by
    rw [three]
    ext <;> (simp only [one_def, mul_def, add_def, _root_.zero_add, add_right_inj]; ring)
  have h2 :
      ((1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z) +
          α * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z) +
          α ^ 2 * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z) =
        ⟨
          (1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z,
          (1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z,
          (1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z
        ⟩ := by
    ext <;> simp only [Int.cast_one, one_def, int_cast_r, mul_def, add_def, α, sq] <;> ring
  rw [h, h2]
  ext <;> (simp only [mul_def, fund, Nat.cast_one, α, one_def, add_def, sq, MulZeroClass.mul_zero,
    _root_.zero_add, _root_.add_zero, _root_.mul_one]; try ring)

-- 3.2.2 The theorem

lemma eq_three_mul_or_eq_three_mul_sub_one_of_fund_zpow_eq_sub_alpha (x : ℤ) (y : ℤ) (n : ℤ)
    (h : fund ^ n = (x : R) + (-y : R) * α) :
    (∃ k : ℤ, n = 3 * k) ∨ (∃ k : ℤ, n = 3 * k - 1) := by
  have nmod3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have hnonneg : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
    have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
    lia
  have neqmod3 := (Int.mul_ediv_add_emod n 3).symm
  have nadd1eqmod3 := (Int.mul_ediv_add_emod (n + 1) 3).symm
  match nmod3 with
  | Or.inl h0 =>
    exact Or.inl ⟨n / 3, by nth_rewrite 1 [neqmod3]; rw [h0]; norm_num⟩
  | Or.inr (Or.inl h1) =>
      set p:= n / 3 with hp
      have neq: n = 3 * p + 1 := by rwa [← h1]
      rw [neq] at h
      have fundpow: fund ^ (3 * p + 1) = fund ^ (3 * p) * fund := by
        rw [zpow_add fund (3 * p) 1, zpow_one, zpow_mul fund 3 p]
      rw [fundpow] at h
      exfalso
      obtain ⟨v, hv⟩ := fund_zpow_three_int_eq_one_add_three_mul p
      push_cast at h
      rw [hv] at h
      have contra := one_add_three_mul_mul_fund_eq_expansion v
      rw [contra] at h
      have h' := congrArg R.z h
      have hz := z_coord_int_add_int_mul_alpha_add_int_mul_alpha_sq x (-y) 0
      have hz2 := z_coord_int_add_alpha_mul_int_add_alpha_sq_mul_int
        (1+3*v.x+6*v.y+6*v.z) (1+3*v.x+3*v.y+6*v.z) (1+3*v.x+3*v.y+3*v.z)
      push_cast at hz
      rw [zero_mul, add_zero] at hz
      rw [hz] at h'
      push_cast at hz2
      push_cast at h'
      rw [hz2] at h'
      lia
  | Or.inr (Or.inr h2) =>
    exact Or.inr ⟨(n + 1) / 3, by
        rw [show (n + 1) % 3 = 0 by lia] at nadd1eqmod3
        lia⟩

-- 3.3 For all natural numbers n≥1 we have u⁽³ⁿ⁾ ≡ 1 + 3ⁿ(α²-α) mod 3ⁿ⁺¹

lemma cubic_expansion : (1 + a)^3 = 1 + 3 * a + 3 * a ^ 2 + a ^ 3 := by ring

lemma exists_add_eq_mul_of_exists_eq_mul
    (h1 : ∃ a', a = c * a') (h2 : ∃ b', b = c * b') :
    ∃ k, a + b = c * k := by
  obtain ⟨a', rfl⟩ := h1
  obtain ⟨b', rfl⟩ := h2
  exact ⟨a' + b', by ring⟩

lemma three_pow_add_two_dvd_three_mul_sq_of_one_le (n : ℕ) (h : 1 ≤ n) :
    ∃ k, 3 * (3 ^ n * a) ^ 2 = 3 ^ (n + 2) * k := by
  use (3^(n-1) * a ^2)
  push_cast; rw [mul_pow, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← pow_mul]
  nth_rewrite 1 [show (3:R) = (3:R) ^ 1 by rw [pow_one]]
  rw [← pow_add, ← pow_add]
  congr 1
  rw [Nat.add_comm]
  nth_rewrite 2 [Nat.add_comm]
  rw [← Nat.add_assoc, add_left_inj]
  nth_rewrite 2 [Nat.add_comm]
  rw [Nat.add_assoc, Nat.sub_add_cancel h]
  ring

lemma three_pow_add_two_dvd_cube_of_one_le (n : ℕ) (h : 1 ≤ n) :
    ∃ k, (3 ^ n * a) ^ 3 = 3 ^ (n + 2) * k := by
  use (3 ^ (2 * n - 2) * a ^ 3)
  push_cast; rw [mul_pow, ← pow_mul, ← mul_assoc]
  congr 1
  rw [← pow_add]
  congr 1
  rw [Nat.add_assoc, Nat.add_sub_cancel' (by simp only [Nat.ofNat_pos, le_mul_iff_one_le_right, h])]
  ring

lemma exists_fund_zpow_three_pow_eq_mod_form_of_one_le (n : ℕ) (h : 1 ≤ n) :
    ∃ k : R,
      (fund ^ (3 ^ n) : R) =
        (3 : ℕ) ^ (n + 1) * (k : R) + (1 : ℕ) + (3 : ℕ) ^ n * (α ^ 2 - α) := by
  set m:= n - 1 with hm
  have hn: n = m + 1 := by lia
  rw [hn]
  induction m with
  | zero =>
    use ⟨2, 2, 1⟩
    simp only [Nat.zero_add, one_add_one_eq_two, pow_one, sq]
    simp only [fund, Nat.cast_one, α, pow_three, Units.val_mul, sq]; ext <;> (ring_nf; rfl)
  | succ m' ih =>
    set n':= m' + 1 with hn'
    obtain ⟨k, hk⟩ := ih
    rw [pow_add, pow_one, pow_mul]; push_cast
    have hkcast: (fund ^ 3 ^ n':R) = ((fund:R) ^ 3 ^ n') := by norm_cast
    rw [hkcast] at hk
    have hkrw :
        ↑(3 ^ (n' + 1)) * k + ↑1 + ↑(3 ^ n') * (α ^ 2 - α) =
          ↑1 + ↑(3 ^ n') * (α ^ 2 - α + 3 * k) := by
      push_cast; rw [pow_add, pow_one]; ring
    push_cast at hk
    push_cast at hkrw
    rw [hkrw] at hk; rw [hk]
    have hn'1: 1 ≤ n' := by rw [hn']; simp
    rw [cubic_expansion]
    have h2: ∃ y, 3 * (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 2 = 3 ^ (n' + 2) * y :=
      three_pow_add_two_dvd_three_mul_sq_of_one_le (α ^ 2 - α + 3 * k) n' hn'1
    have h3: ∃ z, (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 3 = 3 ^ (n' + 2) * z :=
      three_pow_add_two_dvd_cube_of_one_le (α ^ 2 - α + 3 * k) n' hn'1
    have h4 := exists_add_eq_mul_of_exists_eq_mul
      (3 ^ (n' + 2) * k)
      (3 * (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 2)
      (3 ^ (n' + 2)) ⟨k, rfl⟩ h2
    obtain ⟨k1, hk1⟩ := exists_add_eq_mul_of_exists_eq_mul
      (↑(3 ^ (n' + 2)) * k + ↑3 * (↑(3 ^ n') * (α ^ 2 - α + 3 * k)) ^ 2)
      ((3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 3)
      (3 ^ (n' + 2)) h4 h3
    push_cast at hk1
    use k1
    rw [show n' + 1 + 1 = n' + 2 by ring, ←hk1]; push_cast
    nth_rewrite 3 [add_assoc]
    nth_rewrite 7 [add_comm]
    nth_rewrite 1 [← add_assoc]
    congr 1
    nth_rewrite 1 [← add_assoc]
    congr 1
    rw [add_assoc]
    congr
    ring

-- 3.4 Obtaining n

-- 3.4.1 Trick with log

lemma exists_lt_three_pow_of_nonneg (x : ℤ) (h : 0 ≤ x) : ∃ r : ℕ, x < 3 ^ r := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  refine ⟨(Nat.log 3 n).succ, ?_⟩
  exact_mod_cast (Nat.lt_pow_succ_log_self (b := 3) (by norm_num : 1 < 3) n)

-- 3.4.2 If uⁿ = x-yα and n is congruent to 0 modulo 3, then n = 0.

lemma eq_zero_of_forall_emod_three_pow_eq_zero (x : ℤ)
    (h : ∀ (r : ℕ), x % 3 ^ r = 0) : x = 0 := by
  norm_cast at h
  by_cases sign : 0 ≤ x
  · obtain ⟨r, hr⟩ := exists_lt_three_pow_of_nonneg x sign
    exact Int.eq_zero_of_dvd_of_nonneg_of_lt sign hr (Int.dvd_of_emod_eq_zero (h r))
  · have sign' : 0 ≤ -x := by lia
    obtain ⟨r, hr⟩ := exists_lt_three_pow_of_nonneg (-x) sign'
    exact neg_eq_zero.mp <|
      Int.eq_zero_of_dvd_of_nonneg_of_lt sign' hr ((dvd_neg).mpr (Int.dvd_of_emod_eq_zero (h r)))

lemma emod_pow_succ_eq_zero_of_mul_eq (m a : ℤ) (r : ℕ)
    (hdiv : (3 : ℤ) ^ r * a = m) (ha : a % 3 = 0) :
    m % (3 : ℤ) ^ (r + 1) = 0 := by
  norm_num at ha
  obtain ⟨k, hk⟩ := ha
  norm_num
  exact ⟨k, by rw [pow_add, pow_one, Int.mul_assoc, ← hk]; exact hdiv.symm⟩

lemma z_coord_add : (a+b).z = a.z+b.z := rfl

lemma z_coord_int_mul (d : ℤ) : (d * a).z = d * a.z := by
  simp [int_cast_r, mul_def]

lemma z_coord_one_add_int_mul_alpha_sq_sub_alpha (d : ℤ) :
    ((1 : R) + (d : R) * (α ^ 2 - α)).z = d := by
  simp only [int_cast_r, one_def, add_def, neg_def, mul_def, α, sq, sub_eq_add_neg]
  ring

lemma exists_z_eq_mul_add_of_exists_eq_mul_add (d : ℤ) (h : ∃ k, a = d * k + b) :
    ∃ v, a.z = d * v + b.z := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k.z, by rw [z_coord_add, z_coord_int_mul]⟩

lemma exists_z_eq_mul_add_of_one_add_mul (A : R) (M d e : ℤ)
    (h : ∃ k, A = M * k + (1 + d * e * (α ^ 2 - α))) :
    ∃ v : ℤ, A.z = M * v + d * e := by
  obtain ⟨v, hv⟩ := exists_z_eq_mul_add_of_exists_eq_mul_add A (1 + d * e * (α ^ 2 - α)) M h
  exact ⟨v, by
    rw [hv]
    congr
    simpa [mul_assoc] using z_coord_one_add_int_mul_alpha_sq_sub_alpha (d * e)⟩

lemma exists_z_eq_mul_add_of_alpha_sub_mul (A : R) (M d e : ℤ)
    (h : ∃ k, A = M * k + (α + d * e * (2 - α ^ 2) - (1 + d * e * (α ^ 2 - α)))) :
    ∃ v : ℤ, A.z = M * v + (-2) * d * e := by
  obtain ⟨v, hv⟩ := exists_z_eq_mul_add_of_exists_eq_mul_add A
    (α + d * e * (2 - α ^ 2) - (1 + d * e * (α ^ 2 - α))) M h
  exact ⟨v, by
    rw [hv]
    congr
    norm_num [int_cast_r, add_def, neg_def, mul_def, α, sq, sub_eq_add_neg]
    rw [show z 2 = 0 by rfl, show z 1 = 0 by rfl]; ring⟩

lemma exists_fund_pow_three_pow_nat_eq_mod_form (b r : ℕ) (h : 1 ≤ r) :
    ∃ x, ↑((fund ^ 3 ^ r) ^ b) =
      ↑(3 ^ (r + 1)) * x + (1 + ↑(3 ^ r * b) * (α ^ 2 - α)) := by
  induction b with
  | zero => use 0; simp [fund, α]
  | succ n h =>
    obtain ⟨k, hk⟩ := h
    obtain ⟨v, hv⟩ := exists_fund_zpow_three_pow_eq_mod_form_of_one_le r h
    nth_rewrite 1 [pow_add]; rw [pow_one]
    have : ((fund ^ 3 ^ r) ^ n * fund ^ 3 ^ r :Rˣ) = ((fund ^ 3 ^ r) ^ n * (fund ^ 3 ^ r: R)) := by
      norm_cast
    rw [this, hk, hv]
    simp only [add_mul, mul_add, one_mul, Nat.cast_one, Nat.mul_one]; push_cast
    simp only [add_mul, mul_one, ← add_assoc]
    nth_rewrite 1 [add_comm]; simp only [← add_assoc]
    use (
      k * (3 ^ r * (α ^ 2 - α)) +
      3 ^ (r - 1) * n * (α ^ 2 - α) * (α ^ 2 - α) +
      k * (3 ^ (r + 1) * v) + v + 3 ^ r * ↑n * (α ^ 2 - α) * v + k
    )
    congr! 1
    nth_rewrite 1 [add_comm]
    simp only [← add_assoc]
    congr! 1
    congr! 1
    simp only [mul_add]; push_cast
    congr 2
    · congr 2
      · congr 1
        · simp only [← mul_assoc]
        · simp only [← mul_assoc]
          congr 1
          rw [mul_comm]
          simp only [← mul_assoc]
          congr 2
          rw [← pow_add, ← pow_add]
          congr 1
          lia
      · simp only [← mul_assoc]
    · simp only [← mul_assoc]
      congr 1
      ring

lemma inv_eq_of_mul_eq_one (u : Rˣ) (v : R) : u * v = 1 → u⁻¹ = v := by
  intro h
  simpa [mul_assoc] using (congrArg (fun t : R => (u⁻¹ : Rˣ) * t) h).symm

lemma exists_inv_eq_pow_mul_add_of_mul_eq_one_add_pow_mul (u : Rˣ) (v k : R)
    (h : u * v = (1 : R) + (3 : R) ^ (r + 1) * k) :
    ∃ d : R, u⁻¹ = (3 : R) ^ (r + 1) * d + v := by
  use -u⁻¹ * k
  apply inv_eq_of_mul_eq_one; simp only [mul_add]; rw [h]; ring_nf
  rw [show (u:R) * u⁻¹ = 1 by simp]; ring

lemma exists_fund_pow_three_pow_inv_eq_mod_form (r : ℕ) (h : 1 ≤ r) :
    ∃ v : R,
      (fund ^ 3 ^ r) ^ (-1 : ℤ) =
        (3 : R) ^ (r + 1) * v + ((1 : R) - (3 : R) ^ r * (α ^ 2 - α)) := by
  rw [zpow_neg_one]
  obtain ⟨k, hk⟩ := exists_fund_zpow_three_pow_eq_mod_form_of_one_le r h
  have h0 :
      (fund ^ 3 ^ r) * ((1 : R) - (3 : R) ^ r * (α ^ 2 - α)) =
        (1 : R) + (3 : R) ^ (r + 1) *
          (k - (3 : R) ^ r * k * (α ^ 2 - α) -
            (3 : R) ^ (r - 1) * (α ^ 2 - α) * (α ^ 2 - α)) := by
    rw [hk]; push_cast
    nth_rw 2 [sub_eq_add_neg]
    nth_rw 3 [sub_eq_add_neg]
    nth_rw 3 [sub_eq_add_neg]
    simp only [mul_add, add_mul, ← add_assoc, mul_one, one_mul]
    congr 1
    · rw [add_comm]
      simp only [← add_assoc]
      congr 1 <;>
      · ring
    · nth_rw 1 [← neg_one_mul]
      nth_rw 2 [← neg_one_mul]
      simp only [← mul_assoc]
      congr 1
      nth_rw 1 [mul_assoc]
      nth_rw 1 [mul_comm]
      simp only [← mul_assoc]
      congr 1
      nth_rw 3 [mul_comm]
      nth_rw 1 [mul_assoc]
      nth_rw 1 [mul_comm]
      simp only [← mul_assoc]
      congr 1
      rw [← pow_add, ← pow_add]
      congr 1
      lia
  exact exists_inv_eq_pow_mul_add_of_mul_eq_one_add_pow_mul
    (fund ^ 3 ^ r)
    ((1 : R) - (3 : R) ^ r * (α ^ 2 - α))
    (k - (3 : R) ^ r * k * (α ^ 2 - α) - (3 : R) ^ (r - 1) * (α ^ 2 - α) * (α ^ 2 - α))
    h0

lemma exists_fund_pow_three_pow_inv_nat_eq_mod_form (b r : ℕ) (h : 1 ≤ r) :
    ∃ x : R,
      ((fund ^ 3 ^ r) ^ (-1 : ℤ)) ^ b =
        (3 : R) ^ (r + 1) * x + ((1 : R) + (3 : R) ^ r * -↑b * (α ^ 2 - α)) := by
  push_cast
  induction b with
  | zero => use 0; simp [fund, α]
  | succ n h =>
    obtain ⟨k, hk⟩ := h
    obtain ⟨v, hv⟩ := exists_fund_pow_three_pow_inv_eq_mod_form r h
    nth_rewrite 1 [pow_add]; rw [pow_one]
    rw [hk, hv]; push_cast
    simp only [neg_add]
    simp only [add_mul, mul_add, one_mul]
    simp only [← add_assoc]
    nth_rw 4 5 [sub_eq_add_neg]
    simp only [mul_add, ← add_assoc, mul_one]
    rw [add_comm]
    nth_rw 1 [add_assoc]
    nth_rw 7 [add_comm]
    simp only [← add_assoc]
    use (
      3 ^ (r - 1) * n * (α ^ 2 - α) * (α ^ 2 - α) +
      k * 3 ^ (r + 1) * v + v + 3 ^ r * (-n) * (α ^ 2 - α) * v + k * (1 - 3 ^ r * (α ^ 2 - α))
    )
    congr 1
    · congr 2
      simp only [mul_add]
      congr 1
      · congr 1
        · congr 2
          · push_cast
            simp only [← mul_assoc]
            nth_rw 1 [← neg_one_mul]
            nth_rw 2 [← neg_one_mul]
            simp only [← mul_assoc]
            congr 1
            nth_rw 1 [mul_comm]
            nth_rw 2 [mul_comm]
            simp only [← mul_assoc]
            congr 2
            calc
            (3:R) ^ r * (-1:R) * (3:R) ^ r * (-1:R) = (3:R) ^ r * (3:R)^r := by ring
            _ = _ := by
              rw [← pow_add, ← pow_add]
              congr 1
              lia
          · push_cast; ring
        · push_cast; ring
      · push_cast; ring
    · ring

lemma exists_fund_zpow_eq_mod_form (r : ℕ) (a : ℤ) (rpos : 1 ≤ r) :
    ∃ x, ↑((fund ^ (3 : ℤ) ^ r) ^ a) = ↑(3 ^ (r + 1)) * x +
      (↑(1 : ℕ) + ↑(3 ^ r) * ↑a * (α ^ 2 - α)) := by
  obtain ⟨k, hk⟩ := exists_fund_zpow_three_pow_eq_mod_form_of_one_le r rpos
  by_cases apos : 0 ≤ a
  · obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le apos
    simpa [hb] using exists_fund_pow_three_pow_nat_eq_mod_form b r rpos
  · rw [show a = -a.natAbs by
        rw [Int.ofNat_natAbs_of_nonpos (by lia : a ≤ 0)]
        simp]
    nth_rw 1 [← Int.mul_neg_one]
    nth_rw 1 [Int.mul_comm]
    rw [zpow_mul]
    norm_cast
    simp only [Int.reduceNegSucc, Int.reduceNeg]
    push_cast
    simpa using exists_fund_pow_three_pow_inv_nat_eq_mod_form a.natAbs r rpos

theorem eq_zero_of_fund_zpow_eq_sub_alpha_of_eq_three_mul (x : ℤ) (y : ℤ) (n : ℤ)
    (h1 : fund ^ n = (x : R) + (-y : R) * α) (h2 : ∃ k : ℤ, n = 3 * k) : n = 0 := by
  have h: ∀ (r:ℕ), n % 3 ^ r = 0 := by
    intro r
    induction r with
    | zero => rw [pow_zero]; norm_num
    | succ r ih =>
      by_cases rpos: 1 ≤ r
      · set a := n / ((3:ℤ) ^ r) with ha
        have hdiv := Int.mul_ediv_add_emod n (3 ^ r)
        rw [ih] at hdiv
        norm_num at hdiv
        rw [← ha] at hdiv
        apply emod_pow_succ_eq_zero_of_mul_eq n a r hdiv
        norm_num
        have preh0: ∃ x, (fund^n).val = 3 ^ (r+1) * x + (1 + 3 ^ r * a * (α^2 - α)) := by
          simpa [← hdiv, zpow_mul] using exists_fund_zpow_eq_mod_form r a rpos
        obtain ⟨v, hv⟩ : ∃(v:ℤ),((fund^n).val).z =3 ^ (r+1) * v + 3 ^ r * a :=
          exists_z_eq_mul_add_of_one_add_mul (fund^n).val (3 ^ (r+1)) (3 ^ r) a
            preh0
        use (-v)
        have hz : 3 ^ (r+1) * v + 3 ^ r * a = 0 := by
          rw [← hv, h1]
          simpa using z_coord_int_add_int_mul_alpha_add_int_mul_alpha_sq x (-y) 0
        have ha': a * (3:ℤ) ^ r = (3:ℤ) * (-v) * (3:ℤ) ^ r := by
          calc
            a * (3:ℤ) ^ r = (0:ℤ) - (3:ℤ) ^ (r + 1) * v := by lia
            _ = (3:ℤ) * (-v) * (3:ℤ) ^ r := by rw [pow_add]; ring
        exact mul_right_cancel₀ (pow_ne_zero r three_ne_zero) ha'
      · have rpos : r = 0 := by lia
        rw [rpos]; ring_nf
        obtain ⟨k, hk⟩ := h2
        rw [hk]; simp [Int.mul_emod_right]
  exact eq_zero_of_forall_emod_three_pow_eq_zero n h

-- 3.4.3 If uⁿ = x-yα and n is congruent to -1 modulo 3, then n = -1.

theorem eq_neg_one_of_fund_zpow_eq_sub_alpha_of_eq_three_mul_sub_one (x : ℤ) (y : ℤ) (n : ℤ)
    (h1 : fund ^ n = (x : R) + (-y : R) * α) (h2 : ∃ k : ℤ, n = 3 * k - 1) : n = -1 := by
  have h: ∀ (r:ℕ), (n + 1) % 3 ^ r = 0 := by
    intro r
    induction r with
    | zero => rw [pow_zero]; norm_num
    | succ r ih =>
      by_cases rpos: 1 ≤ r
      · set a := (n + 1) / ((3:ℤ) ^ r) with ha
        have hdiv := Int.mul_ediv_add_emod (n + 1) ((3 : ℤ) ^ r)
        have ih' : (n + 1) % ((3 : ℤ) ^ r) = 0 := by simpa using ih
        rw [ih'] at hdiv
        norm_num at hdiv
        rw [← ha] at hdiv
        apply emod_pow_succ_eq_zero_of_mul_eq (n + 1) a r hdiv
        norm_num
        have preh0 :
            ∃ x,
              (fund ^ n).val =
                3 ^ (r + 1) * x +
                  (α + 3 ^ r * a * (2 - α ^ 2) - (1 + 3 ^ r * a * (α ^ 2 - α))) := by
          rw [show n = (3:ℤ) ^ r * a - 1 by lia]
          nth_rw 1 [sub_eq_add_neg]; rw [zpow_add]; push_cast
          rw [fund_inv, zpow_mul]
          obtain ⟨k, hk⟩ := exists_fund_zpow_eq_mod_form r a rpos
          rw [hk]
          use (-k + k*α)
          nth_rw 2 [sub_eq_add_neg]; nth_rw 3 [← mul_neg_one]
          simp only [mul_add, add_mul, ← add_assoc]; push_cast; simp only [one_mul]
          nth_rw 1 [add_assoc]; nth_rw 1 [add_assoc]
          nth_rw 1 [add_comm]; simp only [← add_assoc]
          congr 2
          nth_rw 1 [add_comm]; simp only [← add_assoc]
          congr 1
          · ring
          · nth_rw 1 [mul_assoc]; congr
        obtain ⟨v, hv⟩ :
            ∃(v:ℤ),((fund^n).val).z = 3 ^ (r+1) * v + (-2) * 3 ^ r * a :=
          exists_z_eq_mul_add_of_alpha_sub_mul (fund^n).val (3 ^ (r+1)) (3 ^ r) a
            preh0
        have hz : 3 ^ (r+1) * v + (-2) * 3 ^ r * a = 0 := by
          rw [← hv, h1]
          simpa using z_coord_int_add_int_mul_alpha_add_int_mul_alpha_sq x (-y) 0
        push_cast at hz
        have comp :
            (3 : ℤ) ^ (r + 1) * v + (-2 : ℤ) * (3 : ℤ) ^ r * a =
              ((3 : ℤ) * v - (2 : ℤ) * a) * (3 : ℤ) ^ r := by
          rw [pow_add]; ring
        rw [comp] at hz
        have eqzero: 3 * v = 2 * a := by
          have hsub := (mul_eq_zero.mp hz).resolve_right (pow_ne_zero r three_ne_zero)
          lia
        have dvd : 3 ∣ 2 * a := by
          rw [← eqzero]
          exact dvd_mul_right 3 v
        exact Int.dvd_of_dvd_mul_right_of_gcd_one dvd (by decide)
      · have rpos : r = 0 := by lia
        rw [rpos]; ring_nf
        obtain ⟨k, hk⟩ := h2
        rw [hk]; ring_nf; simp [Int.mul_emod_left]
  have h2:= eq_zero_of_forall_emod_three_pow_eq_zero (n+1) h; lia


-- Section 4: Conclusion

-- 4.1 Equivalence of the problem

theorem norm_one_iff (x y : ℤ) :
    (∃ u : Rˣ, norm u = 1 ∧ x + (-y) * α = u) ↔ x ^ 3 - 2 * y ^ 3 = 1 := by
  constructor
  · rintro ⟨u, h1, h2⟩
    rw [← h1, ← h2]
    simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, int_cast_r, α, add_def, neg_def, mul_def]
    ring_nf
  · intro h
    set u:R := ⟨x, -y, 0⟩ with hu
    have hnorm: norm u = 1 := by
      rw [hu]; simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk]; ring_nf; rw [← h]; ring
    obtain ⟨v, hv⟩ := unit_of_norm u hnorm; refine ⟨v, by simpa [hv] using hnorm, ?_⟩
    rw [hv, hu]; ext <;> simp [int_cast_r, α, add_def, neg_def, mul_def]

-- 4.2 QED

theorem thue (x y : ℤ) (h : x ^ 3 - 2 * y ^ 3 = 1) :
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = -1) := by
  rw [← norm_one_iff] at h
  obtain ⟨u, h1, h2⟩ := h
  obtain ⟨n, hn'⟩ := unit_eq_fund_pow u h1
  have hn: (u:R) = (fund ^ n:R) := by norm_cast
  rw [← h2] at hn
  rcases eq_three_mul_or_eq_three_mul_sub_one_of_fund_zpow_eq_sub_alpha x y n hn.symm with h' | h'
  · have hn0 := eq_zero_of_fund_zpow_eq_sub_alpha_of_eq_three_mul x y n hn.symm h'
    have hn1 : ((x : R) + (-y : R) * α) = (1 : R) := by simpa [hn0] using hn
    have hx : x = 1 := by
      simpa [int_cast_r, α, add_def, neg_def, mul_def, one_def] using
        congrArg R.x hn1
    have hny : -y = 0 := by
      simpa [int_cast_r, α, add_def, neg_def, mul_def, one_def] using
        congrArg R.y hn1
    exact Or.inl ⟨hx, neg_eq_zero.mp hny⟩
  · have hn0 := eq_neg_one_of_fund_zpow_eq_sub_alpha_of_eq_three_mul_sub_one x y n hn.symm h'
    rw [hn0, fund_inv] at hn
    have hx : x = -1 := by
      simpa [int_cast_r, α, add_def, neg_def, mul_def, one_def] using
        congrArg R.x hn
    have hny : -y = 1 := by
      simpa [int_cast_r, α, add_def, neg_def, mul_def, one_def] using
        congrArg R.y hn
    exact Or.inr ⟨hx, (neg_eq_iff_eq_neg).mp hny⟩

end
end R
