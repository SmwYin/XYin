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

lemma add_assoc : a + b + c = a + (b + c) :=
by
  simp only [add_def, mk.injEq]
  ring_nf
  simp

lemma zero_add : 0 + a = a :=
by
  simp only [add_def, zero_def]
  ring_nf

lemma add_zero : a + 0 = a :=
by
  simp only [add_def, zero_def]
  ring_nf

lemma add_comm : a + b = b + a :=
by
  simp only [add_def, mk.injEq]
  ring_nf
  simp

lemma left_distrib : a * (b + c) = a * b + a * c :=
by
  simp only [add_def, mul_def, mk.injEq]
  ring_nf
  simp

lemma right_distrib : (a + b) * c = a * c + b * c :=
by
  simp only [add_def, mul_def, mk.injEq]
  ring_nf
  simp

lemma zero_mul : 0 * a = 0 :=
by
  simp only [zero_def, mul_def, mul_zero]
  ring_nf

lemma mul_zero : a * 0 = 0 :=
by
  simp only [zero_def, mul_def]
  ring_nf

lemma one_mul : 1 * a = a :=
by
  simp only [one_def, mul_def, MulZeroClass.mul_zero, MulZeroClass.zero_mul, _root_.add_zero]
  ring_nf

lemma mul_one : a * 1 = a :=
by
  simp only [one_def, mul_def, MulZeroClass.mul_zero, _root_.add_zero, _root_.zero_add]
  ring_nf

lemma mul_assoc : a * b * c = a * (b * c) :=
by
  simp only [mul_def, mk.injEq]
  ring_nf
  simp

lemma mul_comm : a * b = b * a :=
by
  simp only [mul_def, mk.injEq]
  ring_nf
  simp

lemma add_left_neg : -a + a = 0 :=
by
  simp only [neg_def, add_def, zero_def]
  ring_nf

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
lemma αx : α.x = 0 := rfl

@[simp]
lemma αy : α.y = 1 := rfl

@[simp]
lemma αz : α.z = 0 := rfl

@[simp]
lemma Int_Cast_R (x : ℤ) : (↑x : R) = ⟨x, 0, 0⟩ :=
by
  cases x with
  | ofNat x =>
    induction x with
    | zero =>
      simp only [Int.ofNat_eq_natCast, CharP.cast_eq_zero, Int.cast_zero]
      rfl
    | succ n ih =>
      simp only [Int.ofNat_eq_natCast] at ih
      simp only [
        Int.ofNat_eq_natCast, Nat.cast_succ, Int.cast_add, Int.cast_one, one_def,
        add_def, _root_.add_zero, ih
      ]
  | negSucc x =>
    induction x with
    | zero =>
      simp only [Int.reduceNegSucc, Int.cast_neg, Int.cast_one, Int.reduceNeg]
      rfl
    | succ n ih =>
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev] at ih
      simp only [Int.cast_negSucc, Nat.cast_succ, neg_add_rev]
      rw [ih]
      simp only [Int.negSucc_eq, Nat.cast_succ, neg_add_rev]
      ring_nf
      simp only [one_def, neg_def, neg_zero, add_def, _root_.add_zero, mk.injEq, and_true]
      ring

lemma zcomp (x : ℤ) (y : ℤ) (z : ℤ) : (x + y * α + z * α ^ 2).z = z :=
by
  simp only [add_def, sq, mul_def, αx, αy, αz, Int_Cast_R]
  ring

lemma zcomp' (x : ℤ) (y : ℤ) (z : ℤ) : (x + α * y + α ^ 2 * z).z = z :=
by
  simp only [add_def, sq, mul_def, αx, αy, αz, Int_Cast_R]
  ring

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

lemma rt3_sq : √3^2 = 3 :=
by
  norm_num

lemma hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) :=
by
  exact Real.rpow_pos_of_pos two_pos (1/3)

lemma gtone : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) :=
by
  have h2: (0:ℝ) ≤ 2 := by
    exact zero_le_two
  rw[Real.one_lt_rpow_iff h2]
  left
  constructor <;>
  norm_num

lemma alpha₁_pos : 0 < α₁ :=
by
  exact Real.rpow_pos_of_pos two_pos (1/3)

lemma alpha₁_sq_pos : (0 : ℝ) < α₁ ^ 2 :=
by
  exact pow_pos alpha₁_pos 2

lemma alpha₁_sum_pos₁ : (0:ℝ) < α₁ + α₁ ^ 2 :=
by
  apply add_pos
  · exact alpha₁_pos
  · exact alpha₁_sq_pos

lemma corrolary_alpha₁_sum_pos₁ : (1:ℝ) < (1:ℝ) + α₁ + α₁ ^ 2 :=
by
  have h:= lt_add_of_pos_right 1 alpha₁_sum_pos₁
  rw[← _root_.add_assoc] at h
  exact h

lemma one_lt_alpha₁ : 1 < α₁ :=
by
  norm_num
  exact gtone

lemma one_lt_alpha₁_sq : (1 : ℝ) < α₁ ^ 2 :=
by
  norm_num
  calc
  _ < α₁ := by exact one_lt_alpha₁
  _ = (2:ℝ) ^ (1 / 3:ℝ) := by rfl
  _ ≤ _ := by exact le_abs_self ((2:ℝ) ^ (1 / 3:ℝ))

lemma pre_alpha₁_pow_three : ((2:ℝ) ^ (3:ℕ)) ^ (3⁻¹:ℝ) = (2:ℝ) :=
by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by positivity)]
  simp

@[simp]
lemma alpha₁_pow_three : α₁ ^ 3  = 2 :=
by
  simp only [α₁, one_div, pow_three]
  have h1: (0:ℝ) ≤ 2 := by
    exact zero_le_two
  have h1': (0:ℝ) ≤ 4 := by
    exact zero_le_four
  have h2: ((2:ℝ) * 2) ^ (3⁻¹:ℝ) = (2:ℝ) ^ (3⁻¹:ℝ) * (2:ℝ) ^ (3⁻¹:ℝ) := by
    have h3: ∀ (z:ℝ), (0:ℝ) ≤ 2 → (0:ℝ) ≤ 2 → ((2:ℝ) * 2) ^ z = (2:ℝ) ^ z * (2:ℝ) ^ z := by
      exact fun z _ _ => Real.mul_rpow h1 h1
    exact h3 3⁻¹ h1 h1
  have h2': ((2:ℝ) * 4) ^ (3⁻¹:ℝ) = (2:ℝ) ^ (3⁻¹:ℝ) * (4:ℝ) ^ (3⁻¹:ℝ) := by
    have h3': ∀ (z:ℝ), (0:ℝ) ≤ 2 → (0:ℝ) ≤ 4 → ((2:ℝ) * 4) ^ z = (2:ℝ) ^ z * (4:ℝ) ^ z := by
      exact fun z _ _ => Real.mul_rpow h1 h1'
    exact h3' 3⁻¹ h1 h1'
  have h4: (8:ℝ) ^ (3⁻¹:ℝ) = (2:ℝ) := by
    have h5: (2:ℝ) ^ (3:ℕ) = 8 := by
      simp only [pow_three]
      ring
    rw[← h5]
    exact pre_alpha₁_pow_three
  calc
  _ = (2:ℝ) ^ (3⁻¹:ℝ) * ((2:ℝ) * (2:ℝ)) ^ (3⁻¹:ℝ) := by congr; rw[h2]
  _ = (2:ℝ) ^ (3⁻¹:ℝ) * (4:ℝ) ^ (3⁻¹:ℝ) := by ring_nf
  _ = ((2:ℝ) * (4:ℝ)) ^ (3⁻¹:ℝ):= by rw[h2']
  _ = (8:ℝ) ^ (3⁻¹:ℝ) := by ring
  _ = _ := by rw[h4]

@[simp]
lemma alpha₁_pow_four : α₁ ^ 4  = 2 * α₁ :=
by
  calc
  _ = α₁ * (α₁ ^ 3) := by ring
  _ = α₁ * 2 := by rw[alpha₁_pow_three]
  _ = _ := by ring

@[simp]
lemma alpha₁_pow_five : α₁ ^ 5  = (2:ℝ) * α₁ ^ 2 :=
by
  calc
  _ = α₁ ^ 3 * α₁ ^ 2 := by ring
  _ = _ := by rw[alpha₁_pow_three]

@[simp]
lemma alpha₁_pow_six : α₁ ^ 6  = 4 :=
by
  calc
  _ = α₁ ^ 3 * α₁ ^ 3 := by ring
  _ = 2 * 2 := by simp only [alpha₁_pow_three]
  _ = _ := by ring

lemma omega_conjugate : star ω = - ω - 1 :=
by
  apply Complex.ext
  · simp only [RCLike.star_def, Complex.conj_re, ω_re, Complex.sub_re, Complex.neg_re,
    Complex.one_re]
    ring
  · simp only [RCLike.star_def, Complex.conj_im, ω_im, Complex.sub_im, Complex.neg_im,
    Complex.one_im, sub_zero]

@[simp]
lemma omega_sq : ω ^ 2 = -ω - 1 :=
by
  simp only [pow_two]
  apply Complex.ext
  · simp only [
      Complex.mul_re, ω_re, neg_div, one_div, mul_neg, neg_mul, neg_neg, ω_im,
      Complex.sub_re, Complex.neg_re, Complex.one_re
    ]
    calc
      _ = (4:ℝ) ⁻¹ - √3^2 / 4    := by ring
      _ = 4⁻¹ - 3 / 4            := by simp only [rt3_sq]
      _ = _                      := by ring
  · simp only [
      Complex.mul_im, ω_re, neg_div, one_div, ω_im, neg_mul, mul_neg,
      Complex.sub_im, Complex.neg_im, Complex.one_im, sub_zero
    ]
    ring

@[simp]
lemma omega_pow_three : ω ^ 3 = 1 :=
by
  calc
  _ = ω * ω^2     := by ring
  _ = ω * (-ω-1)  := by simp only [omega_sq]
  _ = -ω^2 - ω    := by ring
  _ = -(-ω-1) - ω := by simp only [omega_sq, neg_sub, sub_neg_eq_add]
  _ = _           := by ring

@[simp]
lemma omega_pow_four : ω ^ 4 = ω :=
by
  calc
  _ = ω * ω^3 := by ring
  _ = ω * 1 := by rw[omega_pow_three]
  _ = _ := by ring

@[simp]
lemma omega_pow_six : ω ^ 6 = 1 :=
by
  calc
  _ = ω ^ (3 * 2) := by ring
  _ = (ω ^ 3) ^ 2 := by ring
  _ = _ := by simp only [omega_pow_three, one_pow]

lemma absomega₂ : ‖ω‖ = (1 : ℝ) :=
by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num
  rw [div_mul_div_comm]
  rw [← sq]
  simp only [rt3_sq]
  norm_num

lemma absomega₁ : ‖-ω - 1‖ = (1 : ℝ) :=
by
  calc
    ‖-ω - 1‖ = ‖ω ^ 2‖ := by rw [← omega_sq]
    _ = ‖ω‖ ^ 2 := by rw [Complex.norm_pow]
    _ = (1 : ℝ) := by rw [absomega₂]; norm_num

@[simp]
lemma alpha₂_pow_three : α₂ ^ 3 = 2 :=
by
  simp only [α₂]
  calc
  _ = α₁^ 3 * ω ^ 3 := by ring_nf; push_cast; ring_nf
  _ = α₁^ 3 * 1:= by rw[omega_pow_three]
  _ = α₁^ 3 := by ring
  _ = _ := by norm_cast; exact alpha₁_pow_three

@[simp]
lemma alpha₂_pow_four : α₂ ^ 4 = 2 * α₂ :=
by
  calc
  _ = α₂ * (α₂ ^ 3) := by ring
  _ = α₂ * 2 := by rw[alpha₂_pow_three]
  _ = _ := by ring

@[simp]
lemma alpha₃_pow_three : α₃ ^ 3 = 2 :=
by
  simp only [α₃, ←omega_sq]
  calc
  _ = α₁ ^ 3 * (ω ^ 2) ^ 3 := by ring_nf; norm_cast; ring_nf
  _ = α₁ ^ 3 * ω ^ 6       := by ring
  _ = α₁ ^ 3 * 1           := by rw[omega_pow_six]
  _ = 2 * 1                := by rw[alpha₁_pow_three]; norm_cast
  _ = _                    := by ring

@[simp]
lemma alpha₃_pow_four : α₃ ^ 4 = 2 * α₃ :=
by
  calc
  _ = α₃ * (α₃ ^ 3) := by ring
  _ = α₃ * 2 := by rw[alpha₃_pow_three]
  _ = _ := by ring

lemma zcompeq {x : R} {y : R} (h : x = y) : x.z = y.z :=
by
  rw [h]

-- 1.4 Ring homomorphism

@[simp]
def σ₁ : R →+* ℝ where
  toFun a   := a.x + a.y * α₁ + a.z * α₁ ^ 2
  map_one'  := by
    simp only [one_def, Int.cast_one, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_mul'  := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]
    ring_nf
    simp only [alpha₁_pow_three, alpha₁_pow_four]
    ring_nf
  map_zero' := by
    simp only [zero_def, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_add'  := by intro x y; simp only [add_def, Int.cast_add]; ring

@[simp]
def σ₂ : R →+* ℂ where
  toFun a := a.x + a.y * α₂ + a.z * α₂ ^ 2
  map_one' := by
    simp only [one_def, Int.cast_one, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_mul' := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]
    ring_nf
    simp only [alpha₂_pow_three, alpha₂_pow_four]
    ring_nf
  map_zero' := by
    simp only [zero_def, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_add' := by intro x y; simp only [add_def, Int.cast_add]; ring

@[simp]
def σ₃ : R →+* ℂ where
  toFun a := a.x + a.y * α₃ + a.z * α₃ ^ 2
  map_one' := by
    simp only [one_def, Int.cast_one, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_mul' := by
    intro x y
    simp only [mul_def, Int.cast_add, Int.cast_mul]
    ring_nf
    simp only [alpha₃_pow_three, alpha₃_pow_four]
    ring_nf
  map_zero' := by
    simp only [zero_def, Int.cast_zero, MulZeroClass.zero_mul, _root_.add_zero]
  map_add' := by intro x y; simp only [add_def, Int.cast_add]; ring

lemma pow_sigma_eq_sigma_pow (u : Rˣ) (n : ℤ) : σ₁ u ^ n = σ₁ (u ^ n) :=
by
  cases n with
  | ofNat _ =>
    simp only [
      σ₁, α₁, one_div, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow
    ]
  | negSucc _ =>
    simp only [
      σ₁, α₁, one_div, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      zpow_negSucc, map_units_inv, Units.val_pow_eq_pow_val, map_pow
    ]

lemma sigma_conjugate : σ₃ a = star (σ₂ a) :=
by
  refine Complex.ext_iff.2 ?_
  constructor <;> simp [σ₃, σ₂, α₃, α₂, omega_conjugate]

lemma sigma_abs_eq : ‖σ₂ a‖ = ‖σ₃ a‖ :=
by
  rw [sigma_conjugate]
  simpa using (Complex.norm_conj (σ₂ a)).symm

lemma sigma_prod : σ₂ a * σ₃ a = ((‖σ₂ a‖) ^ 2 : ℝ) :=
by
  rw [sigma_conjugate]
  simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (σ₂ a)

-- 1.5 Norm

@[simp]
def norm : R →* ℤ where
  toFun a := a.x^3 + 2*a.y^3 + 4*a.z^3 - 6*a.x*a.y*a.z
  map_one' := by simp only [Nat.cast_ofNat]; exact rfl
  map_mul' := by intro x y; simp only [mul_def, Nat.cast_ofNat]; ring

lemma norm_eq_emb_prod : norm a = σ₁ a * σ₂ a * σ₃ a :=
by
  simp only [
    norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub, Int.cast_add,
    Int.cast_pow, Int.cast_mul, σ₁, RingHom.coe_mk, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, σ₂, σ₃, α₂, α₃
  ]
  ring_nf
  norm_cast
  simp only [alpha₁_pow_three, alpha₁_pow_four, alpha₁_pow_five, alpha₁_pow_six, omega_pow_four]
  ring_nf
  norm_num
  ring

lemma norm_eq_emb_prod₂ : norm a = σ₁ a * ‖σ₂ a‖ ^ 2 :=
by
  have h:= norm_eq_emb_prod a
  rw[_root_.mul_assoc] at h
  rw[sigma_prod a] at h
  norm_cast at h

-- 1.6 Units

-- 1.6.1 General properties

lemma unit_of_norm (h : norm a = 1) : ∃ u : Rˣ, u = a :=
by
  let u : Rˣ := {
    val := a
    inv := ⟨a.x ^ 2 - 2 * a.y * a.z, 2 * a.z ^ 2 - a.x * a.y, a.y ^ 2 - a.x * a.z⟩
    val_inv := by ext
                  · simp only [one_def]
                    rw [← h]
                    simp only [Nat.cast_ofNat, mul_def, norm, MonoidHom.coe_mk, OneHom.coe_mk]
                    ring
                  · simp only [Nat.cast_ofNat, mul_def, one_def]
                    ring
                  · simp only [Nat.cast_ofNat, mul_def, one_def]
                    ring
    inv_val := by ext
                  · simp only [one_def]
                    rw [← h]
                    simp only [Nat.cast_ofNat, mul_def, norm, MonoidHom.coe_mk, OneHom.coe_mk]
                    ring
                  · simp only [Nat.cast_ofNat, mul_def, one_def]
                    ring
                  · simp only [Nat.cast_ofNat, mul_def, one_def]
                    ring
  }
  use u

lemma abs_sq_pos (h : norm a = 1) : (0 : ℝ) < ‖σ₂ a‖ ^ 2 :=
by
  have h1 := sq_nonneg ‖σ₂ a‖
  have h2 : (‖σ₂ a‖ ^ 2 : ℝ) ≠ 0 := by
    by_contra nh
    have neg: (norm a:ℝ) = 0 := by
      rw[norm_eq_emb_prod₂ a]
      rw[nh]
      ring
    rw[Int.cast_eq_zero] at neg
    rw[h] at neg
    have contra: ¬ (1:ℤ) = 0 := by
      exact one_ne_zero
    contradiction
  exact lt_of_le_of_ne h1 h2.symm

lemma sigma_norm_one_pos (h : norm a = 1) : 0 < σ₁ a :=
by
  by_contra nh
  push Not at nh
  have nA: norm a ≤ (0:ℝ) := by
    rw[norm_eq_emb_prod₂]
    calc
    _ ≤ (0:ℝ) * ‖σ₂ a‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right nh (le_of_lt (abs_sq_pos a h))
    _ = _ := by exact MulZeroClass.zero_mul (‖σ₂ a‖ ^ 2)
  rw [Int.cast_nonpos] at nA
  have neg: ¬ norm a ≤ 0 := by
    push Not
    calc
    _ < (1:ℤ) := by exact Int.one_pos
    _ = _ := by exact h.symm
  contradiction

lemma sigma_unit_neq_zero (u : Rˣ) : σ₁ u.val ≠ 0 :=
by
  by_contra h
  have h1: σ₁ u.val * σ₁ u.inv = 1 := by
    calc
    _ = σ₁ (u.val * u.inv) := by simp only [RingHom.map_mul]
    _ = σ₁ (1)             := by congr; exact u.val_inv
    _ = _                  := by exact RingHom.map_one σ₁
  have h2: σ₁ u.val * σ₁ u.inv = 0 := by
    calc
    _ = 0 * σ₁ u.inv := by rw[h]
    _ = _ := by exact MulZeroClass.zero_mul (σ₁ u.inv)
  rw[h2] at h1
  have hc: ¬ (0:ℝ) = 1 := by
    push Not
    exact zero_ne_one
  contradiction

lemma abs_sigma_unit_pos (u : Rˣ) : 0 < |σ₁ u.val| :=
by
  rw[abs_pos]
  exact sigma_unit_neq_zero u

-- 1.6.2 The fundamental unit

@[simp]
def fund : Rˣ where
  val := 1 + α + α^2
  inv := α - 1
  val_inv := by simp only [Nat.cast_one, α]; ring_nf; rfl
  inv_val := by simp only [α, Nat.cast_one]; ring_nf; rfl

lemma fundx : fund.val.x = 1 := rfl

lemma fundy : fund.val.y = 1 := rfl

lemma fundz : fund.val.z = 1 := rfl

lemma fund_inv : fund ^ (-1:ℤ) = -1 + α :=
by
  simp only [fund, Nat.cast_one, α, zpow_neg, zpow_one, Units.inv_mk]
  ring

lemma norm_fund : norm fund = 1 :=
by
  rfl

lemma norm_fund_inv : norm (fund⁻¹:Rˣ) = 1 :=
by
  rfl

lemma norm_fund_pow (n : ℤ) : norm (fund ^ n) = 1 :=
by
  cases n with
  | ofNat n =>
    change norm ((fund : R) ^ n) = 1
    calc
      norm ((fund : R) ^ n) = norm (fund : R) ^ n := map_pow norm (fund : R) n
      _ = 1 := by rw [norm_fund]; norm_num
  | negSucc n =>
    change norm (((fund⁻¹ : Rˣ) : R) ^ (n + 1)) = 1
    calc
      norm (((fund⁻¹ : Rˣ) : R) ^ (n + 1)) = norm ((fund⁻¹ : Rˣ) : R) ^ (n + 1) := by
        exact map_pow norm ((fund⁻¹ : Rˣ) : R) (n + 1)
      _ = 1 := by rw [norm_fund_inv]; norm_num

lemma fund_pow_cancel (n : ℤ) : fund ^ (-n) * fund ^ n = 1 :=
by
  rw[← zpow_add fund (-n) n]
  have h: -n + n = 0 := by
    exact Int.add_left_neg n
  rw[h]
  exact rfl

lemma fund_mul_pow (n : ℤ) : fund * fund ^ n = fund ^ (n + 1) :=
by
  have h: fund = fund ^ (1:ℤ) := by
    exact rfl
  nth_rewrite 1 [h]
  have h2: n + 1 = 1 + n := by
    exact Int.add_comm n 1
  rw[h2]
  exact (zpow_add fund 1 n).symm

lemma sigma_fund_pos : 0 < σ₁ fund :=
by
  simp only [
    fund, α, σ₁, Nat.cast_one, map_add, map_one, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Int.cast_zero, Int.cast_one, _root_.one_mul, _root_.zero_add,
    MulZeroClass.zero_mul, _root_.add_zero, map_pow
  ]
  apply add_pos
  · apply add_pos
    · exact Real.zero_lt_one
    · exact alpha₁_pos
  · exact alpha₁_sq_pos

lemma sigma_fund_inv (n : ℤ) : 0 < σ₁ (fund ^ n) :=
by
  rw [← pow_sigma_eq_sigma_pow]
  exact zpow_pos sigma_fund_pos n

lemma fund_pow_sub (n : ℤ) : fund ^ (n + 1) * fund ^ (-n) = fund :=
by
  rw[← zpow_add fund (n+1) (-n)]
  have h: n + 1 + (- n) = 1 := by
    ring
  rw[h]
  exact rfl


-- Section 2: Every element of ℤ[α] with norm 1 is a power of fund

-- 2.1 Finding the exponent with log

noncomputable def ℓ : Rˣ → ℝ := fun u ↦ Real.log |σ₁ u.val|

lemma step0 : ℓ fund > 0 :=
by
  have h1: 1 < |σ₁ fund.val| := by
    simp only [fund, α, σ₁, Nat.cast_one, map_add, map_one, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Int.cast_zero, Int.cast_one, _root_.one_mul, _root_.zero_add,
    MulZeroClass.zero_mul, _root_.add_zero, map_pow]
    rw[lt_abs]
    left
    exact corrolary_alpha₁_sum_pos₁
  have h: 0 < Real.log |σ₁ fund.val| := by
    calc
    _ = Real.log (1) := by exact Real.log_one.symm
    _ < _ := by exact Real.log_lt_log one_pos h1
  exact h

lemma floor_pow (u : Rˣ) (h : norm u = 1) :
    ∃ n : ℤ, σ₁ (fund ^ n) ≤ σ₁ u ∧ σ₁ u < σ₁ (fund ^ (n + 1)) :=
by
  let n:= Int.floor (ℓ u / ℓ fund)
  use n
  have hle1: n ≤ ℓ u / ℓ fund := by
    exact Int.floor_le (ℓ u / ℓ fund)
  have hl1: ℓ u / ℓ fund < n + 1 := by
    exact Int.lt_floor_add_one (ℓ u / ℓ fund)
  have h': 0 < ℓ fund := by
    exact step0
  have h'': ℓ fund ≠ 0 := by
    exact ne_of_gt h'
  have hle2: n * ℓ fund ≤ ℓ u := by
    calc
    _ ≤ (ℓ u / ℓ fund) * ℓ fund := by
      exact mul_le_mul_of_nonneg_right hle1 h'.le
    _ = _ := by simp only [div_mul, div_self h'', div_one]
  have hl2: ℓ u < (n + 1) * ℓ fund := by
    calc
    _ = (ℓ u / ℓ fund) * ℓ fund := by simp only [div_mul, div_self h'', div_one]
    _ < _ := by exact mul_lt_mul_of_pos_right hl1 h'
  have he1: n * ℓ fund = Real.log (|σ₁ fund.val|^n) := by
    have he1': n * Real.log |σ₁ fund.val| = Real.log (|σ₁ fund.val|^n) := by
      rw[Real.log_zpow]
    exact he1'
  have he2: (n + 1) * ℓ fund = Real.log (|σ₁ fund.val|^(n+1)) := by
    have he2': (n + 1) * Real.log |σ₁ fund.val| = Real.log (|σ₁ fund.val|^(n+1)) := by
      rw[Real.log_zpow]; norm_cast
    exact he2'
  rw [he1] at hle2
  rw [he2] at hl2
  have hle2': Real.log (|σ₁ fund.val| ^ n) ≤ Real.log (|σ₁ u.val|) := by
    exact hle2
  have hl2': Real.log (|σ₁ u.val|) < Real.log (|σ₁ fund| ^ (n + 1)) := by
    exact hl2
  have h01: 0 < |σ₁ fund.val| := by
    exact abs_sigma_unit_pos fund
  have h01': 0 < |σ₁ fund.val| ^ n := by
    exact zpow_pos h01 n
  have h02: 0 < |σ₁ u.val| := by
    exact abs_sigma_unit_pos u
  have h02': 0 < |σ₁ fund.val| ^ (n + 1) := by
    exact zpow_pos h01 (n + 1)
  have hle3: |σ₁ fund.val| ^ n ≤ |σ₁ u.val| := by
    rw [Real.log_le_log_iff h01' h02] at hle2'
    exact hle2'
  have hl3: |σ₁ u.val| < |σ₁ fund.val| ^ (n + 1) := by
    rw [Real.log_lt_log_iff h02 h02'] at hl2'
    exact hl2'
  have hle3': (σ₁ fund.val) ^ n ≤ σ₁ u.val := by
    calc
    _ = |σ₁ fund.val| ^ n := by congr; exact (abs_of_pos sigma_fund_pos).symm
    _ ≤ |σ₁ u.val| := by exact hle3
    _ = _ := by exact abs_of_pos (sigma_norm_one_pos u h)
  have hl3': σ₁ u.val < (σ₁ fund.val) ^ (n + 1) := by
    calc
    _ = |σ₁ u.val| := by exact (abs_of_pos (sigma_norm_one_pos u h)).symm
    _ < |σ₁ fund.val| ^ (n + 1) := by exact hl3
    _ = _ := by congr; exact (abs_of_pos sigma_fund_pos)
  rw [pow_sigma_eq_sigma_pow] at hle3'
  rw [pow_sigma_eq_sigma_pow] at hl3'
  constructor
  · exact hle3'
  · exact hl3'

-- 2.2  Bound on σ₁ fund

lemma rpow_inv_rpow (x : ℝ) (y : ℝ) (hx : 0 ≤ x) (hy : y ≠ 0) :
    (x ^ y⁻¹) ^ y = x := by
  rw [← Real.rpow_mul hx, inv_mul_cancel₀ hy, Real.rpow_one]

lemma le_rpow_inv_iff_of_pos (x : ℝ) (y : ℝ) (z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← Real.rpow_le_rpow_iff hx _ hz, rpow_inv_rpow] <;> positivity

lemma rpow_inv_lt_iff_of_pos (x : ℝ) (y : ℝ) (z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    x ^ z⁻¹ < y ↔ x < y ^ z :=
  lt_iff_lt_of_le_iff_le <| le_rpow_inv_iff_of_pos y x z hy hx hz

lemma approx1 : (2 : ℝ) ^ ((1 / 3) : ℝ) < 13 / 10 :=
by
  rw [one_div]
  have h': (10:ℝ) ^ (3:ℕ) = 1000 := by
    rw [pow_three]
    ring
  rw [← Real.rpow_natCast] at h'
  have h'': (10:ℝ) ^ (3:ℝ) = 1000 := by
    exact h'
  have h'2: (13:ℝ) ^ (3:ℕ) = 2197 := by
    rw [pow_three]
    ring
  rw [← Real.rpow_natCast] at h'2
  have h''2: (13:ℝ) ^ (3:ℝ) = 2197 := by
    exact h'2
  have h13: 0 ≤ (13:ℝ) := by
    norm_num
  have h10: 0 ≤ (10:ℝ) := by
    norm_num
  have h10cube: 0 < (10:ℝ) ^ (3:ℝ) := by
    rw [h'']
    norm_num
  have h1: (0:ℝ) ≤ 13 / 10 := by
    norm_num
  rw [rpow_inv_lt_iff_of_pos  2 (13/10) 3 zero_le_two h1 zero_lt_three]
  rw [Real.div_rpow h13 h10]
  rw [lt_div_iff₀ h10cube]
  rw [h'', h''2]
  norm_num

lemma approx2 : ((2 : ℝ) ^ ((1 / 3) : ℝ)) ^ 2 < 169 / 100 :=
by
  have pos: (0:ℝ) < (13:ℝ) / (10:ℝ) := by
    norm_num
  have compsq: (169:ℝ) / (100:ℝ) = ((13:ℝ) / (10:ℝ)) ^ 2 := by
    rw[sq]
    norm_num
  rw[compsq]
  rw[sq_lt_sq]
  rw [abs_of_pos hpos]
  rw [abs_of_pos pos]
  exact approx1

lemma pre_sigma_fund_bound :
    (2 : ℝ) ^ ((1 / 3) : ℝ) + ((2 : ℝ) ^ ((1 / 3) : ℝ)) ^ 2 < (3 : ℝ) :=
by
  nlinarith [approx1, approx2]

lemma sigma_fund_bound : σ₁ fund < 4 :=
by
  simp only [fund, α, σ₁, α₁, Nat.cast_one, map_add, map_one, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Int.cast_zero, Int.cast_one, _root_.one_mul, _root_.zero_add,
    MulZeroClass.zero_mul, _root_.add_zero, map_pow]
  nlinarith [pre_sigma_fund_bound]

-- 2.3 Bounds on coefficients

-- 2.3.1 Solving linear system

lemma x_eq : |3 * a.x - σ₁ a| = ‖σ₂ a + σ₃ a‖ :=
by
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

lemma y_eq : |3 * α₁ * a.y - σ₁ a| = ‖(-ω - 1) * σ₂ a + ω * σ₃ a‖ :=
by
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

lemma z_eq : |3 * α₁^2 * a.z - σ₁ a| = ‖ω * σ₂ a + (-ω - 1) * σ₃ a‖ :=
by
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

lemma bound_comp (x : ℝ) (y : ℝ) (h1 : y < 4) (h2 : 3 * x - y ≤ 2) : x < 2 :=
by
  nlinarith

lemma bound_comp2 (x : ℝ) (y : ℝ) (h1 : 1 ≤ y) (h2 : y - 3 * x ≤ 2) : -3⁻¹ ≤ x :=
by
  nlinarith

lemma bound_comp3 (x : ℝ) (y : ℝ) (h1 : 1 < y) (h2 : y * x < 2) : x < 2 :=
by
  nlinarith

lemma bound_comp4 (x : ℤ) : x < (2 : ℝ) ↔ x ≤ 1 :=
by
  constructor
  · intro h
    by_contra nh
    push Not at nh
    have negh: ¬ x < (2:ℝ) := by
      push Not
      norm_cast
    contradiction
  · intro h
    calc
    _ ≤ (1:ℝ) := by norm_cast
    _ < _ := by exact one_lt_two

lemma bound_comp5 (x : ℝ) (y : ℝ) (h1 : 1 < y) (h2 : -3⁻¹ ≤ y * x) : -3⁻¹ < x :=
by
  by_contra nh
  push Not at nh
  have nh2: ¬ -3⁻¹ ≤ y * x := by
    push Not
    have hneg: x < 0 := by
      calc
      _ ≤ (-3⁻¹:ℝ) := by exact nh
      _ < _ := by norm_num
    calc
    _ < 1 * x := by exact mul_lt_mul_of_neg_right h1 hneg
    _ = x := by ring
    _ ≤ _ := by exact nh
  contradiction

lemma bound_comp6 (x : ℤ) : -3⁻¹ ≤ (x : ℝ) ↔ 0 ≤ x :=
by
  constructor
  · intro h
    by_contra nh
    push Not at nh
    have negh: ¬ (-3⁻¹:ℝ) ≤ ↑x := by
      push Not
      calc
      (x:ℝ) ≤ -1 := by exact Int.cast_le_neg_one_of_neg nh
      _ < _ := by norm_num
    contradiction
  · intro h
    have h': (-3⁻¹:ℝ) < x := by
      calc
      (-3⁻¹:ℝ) < (0:ℝ) := by norm_num
      _ ≤ _ := by exact_mod_cast h
    exact le_of_lt h'

lemma bound_comp6' (x : ℤ) : -3⁻¹ < (x : ℝ) ↔ 0 ≤ x :=
by
  constructor
  · intro h
    have h': -3⁻¹ ≤ (x:ℝ) := by
      exact le_of_lt h
    rw[bound_comp6] at h'
    exact h'
  · intro h
    calc
    (-3⁻¹:ℝ) < (0:ℝ) := by norm_num
    _ ≤ _ := by exact_mod_cast h

lemma bound_comp7 (x : ℤ) (h1 : x ≤ 1) (h2 : 0 ≤ x) : x = 0 ∨ x = 1 :=
by
  by_contra nh
  push Not at nh
  obtain ⟨nh1, nh2⟩ := nh
  have h1':= lt_of_le_of_ne h1 nh2
  have h2':= lt_of_le_of_ne h2 nh1.symm
  have nh1': ¬ x < 1 := by
    push Not
    exact h2'
  contradiction

-- 2.3.3 Checking possible values

lemma check_cases (A : Rˣ) (h : norm A = 1)
    (h1 : (A : R).x = 0 ∨ (A : R).x = 1)
    (h2 : (A : R).y = 0 ∨ (A : R).y = 1)
    (h3 : (A : R).z = 0 ∨ (A : R).z = 1) :
    A = (1 : Rˣ) ∨ A = fund :=
by
  cases h1 with
  | inl h1 =>
    cases h2 with
    | inl h2 =>
      cases h3 with
      | inl h3 =>
        have nA: norm A = 0 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, h2, MulZeroClass.mul_zero,
            _root_.add_zero, h3, sub_self
          ]
        rw[nA] at h
        have neg: ¬ (0:ℤ) = 1 := by
          push Not
          exact Int.zero_ne_one
        contradiction
      | inr h3 =>
        have nA: norm A = 4 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, h2, MulZeroClass.mul_zero,
            _root_.add_zero, h3, one_pow, _root_.mul_one, _root_.zero_add, sub_zero
          ]
        rw[nA] at h
        have neg: ¬ (4:ℤ) = 1 := by
          push Not
          exact OfNat.ofNat_ne_one 4
        contradiction
    | inr h2 =>
      cases h3 with
      | inl h3 =>
        have nA: norm A = 2 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, h2,
            MulZeroClass.mul_zero, h3
          ]
          norm_num
        rw[nA] at h
        have neg: ¬ (2:ℤ) = 1 := by
          push Not
          exact OfNat.ofNat_ne_one 2
        contradiction
      | inr h3 =>
        have nA: norm A = 6 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, h2,
            MulZeroClass.mul_zero, h3
          ]
          norm_num
        rw[nA] at h
        have neg: ¬ (6:ℤ) = 1 := by
          push Not
          exact OfNat.ofNat_ne_one 6
        contradiction
  | inr h1 =>
    cases h2 with
    | inl h2 =>
      cases h3 with
      | inl h3 =>
        left
        ext
        · simp only [h1, Units.val_one]; rfl
        · simp only [h2, Units.val_one]; rfl
        · simp only [h3, Units.val_one]; rfl
      | inr h3 =>
        have nA: norm A = 5 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, h2,
            MulZeroClass.mul_zero, h3
          ]
          norm_num
        rw[nA] at h
        have neg: ¬ (5:ℤ) = 1 := by
          push Not
          exact OfNat.ofNat_ne_one 5
        contradiction
    | inr h2 =>
      cases h3 with
      | inl h3 =>
        have nA: norm A = 3 := by
          simp only [
            norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, h1, h2,
            MulZeroClass.mul_zero, h3
          ]
          norm_num
        rw[nA] at h
        have neg: ¬ (3:ℤ) = 1 := by
          push Not
          exact OfNat.ofNat_ne_one 3
        contradiction
      | inr h3 =>
        right
        ext
        · simp only [h1, fund, Nat.cast_one, α]; rfl
        · simp only [h2, fund, Nat.cast_one, α]; rfl
        · simp only [h3, fund, Nat.cast_one, α]; rfl

-- 2.4 The theorem

lemma sq_gt_1 (x : ℝ) (h : 1 < x) : ((1 : ℝ) < x ^ 2) :=
by
  nlinarith

theorem unit_eq_fund_pow (u : Rˣ) (h : norm u = 1) : ∃ n : ℤ, u = fund ^ n :=
by
  obtain ⟨n, hn1, hn2⟩:= floor_pow u h
  let A:= u * fund ^ (-n)
  have hnormA: norm A = 1 := by
    calc
    _ = norm u * norm (fund ^ (-n)) := by exact MonoidHom.map_mul norm u (fund ^ (-n))
    _ = 1 * norm (fund ^ (-n)) := by rw[h]
    _ = norm (fund ^ (-n)) := by exact Int.one_mul (norm (fund ^ (-n)))
    _ = 1 := by exact norm_fund_pow (-n)
  have h': 0 < σ₁ (fund ^ (-n)) := by
    exact sigma_fund_inv (-n)
  have hA1: (1:ℝ) ≤ σ₁ A := by
    calc
    _ = σ₁ 1 := by exact (RingHom.map_one σ₁).symm
    _ = σ₁ (fund ^ n * fund ^ (-n)) := by
      congr
      simp only [fund, Nat.cast_one, α, zpow_neg, Units.mul_inv]
    _ = σ₁ (fund ^ n) * σ₁ (fund ^ (-n)) := by exact RingHom.map_mul σ₁ (fund ^ n) (fund ^ (-n))
    _ ≤ σ₁ u * σ₁ (fund ^ (-n)) := by exact mul_le_mul_of_nonneg_right hn1 h'.le
    _ = _ := by exact (RingHom.map_mul σ₁ u (fund ^ (-n))).symm
  have hApos: 0 < σ₁ A := by
    exact sigma_norm_one_pos A hnormA
  have hA2: σ₁ A < σ₁ fund := by
    calc
    _ = σ₁ u * σ₁ (fund ^ (-n)) := by exact (RingHom.map_mul σ₁ ↑u ↑(fund ^ (-n)))
    _ < σ₁ (fund ^ (n + 1)) * σ₁ (fund ^ (-n)) := by exact mul_lt_mul_of_pos_right hn2 h'
    _ = σ₁ (fund ^ (n + 1) * fund ^ (-n)) := by
      exact (RingHom.map_mul σ₁ (fund ^ (n + 1)) (fund ^ (-n))).symm
    _ = _ := by congr; norm_cast; exact fund_pow_sub n
  have hσ₂A : ‖σ₂ A‖ ≤ 1 := by
    by_contra hσ₂A
    push Not at hσ₂A
    have nhnormA : (1 : ℤ) < norm A := by
      have nhnormA' : (1 : ℤ) < σ₁ A * ‖σ₂ A‖ ^ 2 := by
        calc
        _ = (1:ℝ) := by exact Int.cast_one
        _ ≤ σ₁ A := by exact hA1
        _ = σ₁ A * (1:ℝ) := by simp
        _ < _ := by exact mul_lt_mul_of_pos_left (sq_gt_1 ‖σ₂ A‖ hσ₂A) hApos
      rw [← norm_eq_emb_prod₂ A] at nhnormA'
      norm_cast at nhnormA'
    have neghnormA: ¬ norm A = 1 := by
      push Not
      exact Int.ne_of_gt nhnormA
    contradiction
  have A.x_bound: |3 * (A:R).x - σ₁ A| ≤ 2 := by
    calc
    _ = ‖σ₂ A + σ₃ A‖ := by exact x_eq A
    _ ≤ ‖σ₂ A‖ + ‖σ₃ A‖ := by simpa using norm_add_le (σ₂ A) (σ₃ A)
    _ = ‖σ₂ A‖ + ‖σ₂ A‖ := by rw [← sigma_abs_eq]
    _ ≤ 2 := by nlinarith [hσ₂A]
  have A.y_bound: |3 * α₁ * (A:R).y - σ₁ A| ≤ 2 := by
    calc
    _ = ‖((-ω - 1) * σ₂ A) + (ω * σ₃ A)‖ := by exact y_eq A
    _ ≤ ‖(-ω - 1) * σ₂ A‖ + ‖ω * σ₃ A‖ := by
      simpa using norm_add_le ((-ω - 1) * σ₂ A) (ω * σ₃ A)
    _ = ‖-ω - 1‖ * ‖σ₂ A‖ + ‖ω‖ * ‖σ₃ A‖ := by rw [Complex.norm_mul, Complex.norm_mul]
    _ = (1 : ℝ) * ‖σ₂ A‖ + (1 : ℝ) * ‖σ₂ A‖ := by rw [absomega₁, absomega₂, ← sigma_abs_eq]
    _ = ‖σ₂ A‖ + ‖σ₂ A‖ := by simp only [_root_.one_mul ‖σ₂ A‖]
    _ ≤ 2 := by nlinarith [hσ₂A]
  have A.z_bound: |(3:ℝ) * α₁^2 * (A:R).z - σ₁ A| ≤ 2 := by
    calc
    _ = ‖ω * σ₂ A + (-ω - 1) * σ₃ A‖ := by exact z_eq A
    _ ≤ ‖ω * σ₂ A‖ + ‖(-ω - 1) * σ₃ A‖ := by
      simpa using norm_add_le (ω * σ₂ A) ((-ω - 1) * σ₃ A)
    _ = ‖ω‖ * ‖σ₂ A‖ + ‖-ω - 1‖ * ‖σ₃ A‖ := by rw [Complex.norm_mul, Complex.norm_mul]
    _ = (1 : ℝ) * ‖σ₂ A‖ + (1 : ℝ) * ‖σ₂ A‖ := by rw [absomega₁, absomega₂, ← sigma_abs_eq]
    _ = ‖σ₂ A‖ + ‖σ₂ A‖ := by simp only [_root_.one_mul ‖σ₂ A‖]
    _ ≤ 2 := by nlinarith [hσ₂A]
  rw [abs_sub_le_iff] at A.x_bound
  rw [abs_sub_le_iff] at A.y_bound
  rw [abs_sub_le_iff] at A.z_bound
  obtain ⟨A.x1, A.x2⟩ := A.x_bound
  obtain ⟨A.y1, A.y2⟩ := A.y_bound
  obtain ⟨A.z1, A.z2⟩ := A.z_bound
  have hAb: σ₁ A < 4 := by
    calc
    _ < σ₁ fund := by exact hA2
    _ < 4 := by exact sigma_fund_bound
  have A.x11 := bound_comp (A:R).x (σ₁ A) hAb A.x1
  rw[_root_.mul_assoc] at A.y1
  have A.y11 := bound_comp (α₁ * (A:R).y) (σ₁ A) hAb A.y1
  rw[_root_.mul_assoc] at A.z1
  have A.z11 := bound_comp (α₁ ^ 2 * (A:R).z) (σ₁ A) hAb A.z1
  have A.x21 := bound_comp2 (A:R).x (σ₁ A) hA1 A.x2
  rw[_root_.mul_assoc] at A.y2
  have A.y21 := bound_comp2 (α₁ * (A:R).y) (σ₁ A) hA1 A.y2
  rw[_root_.mul_assoc] at A.z2
  have A.z21 := bound_comp2 (α₁ ^ 2 * (A:R).z) (σ₁ A) hA1 A.z2
  have A.y12 := bound_comp3 (A:R).y α₁ one_lt_alpha₁ A.y11
  have A.z12 := bound_comp3 (A:R).z (α₁^2) one_lt_alpha₁_sq A.z11
  rw[bound_comp4 (A:R).x] at A.x11
  rw[bound_comp4 (A:R).y] at A.y12
  rw[bound_comp4 (A:R).z] at A.z12
  have A.y22 := bound_comp5 (A:R).y α₁ one_lt_alpha₁ A.y21
  have A.z22 := bound_comp5 (A:R).z (α₁^2) one_lt_alpha₁_sq A.z21
  rw[bound_comp6 (A:R).x] at A.x21
  rw[bound_comp6' (A:R).y] at A.y22
  rw[bound_comp6' (A:R).z] at A.z22
  have A.x_value := bound_comp7 (A:R).x A.x11 A.x21
  have A.y_value := bound_comp7 (A:R).y A.y12 A.y22
  have A.z_value := bound_comp7 (A:R).z A.z12 A.z22
  have A_value := check_cases A hnormA A.x_value A.y_value A.z_value
  cases A_value with
  | inl h1 =>
    use n
    calc
    _ = u * 1 := by rw [_root_.mul_one u]
    _ = u * (fund ^ (-n) * fund ^ n) := by rw[fund_pow_cancel n]
    _ = u * fund ^ (-n) * fund ^ n := by rw[← _root_.mul_assoc]
    _ = A * fund ^ n := by exact rfl
    _ = 1 * fund ^ n := by rw[h1]
    _ = _ := by exact (_root_.one_mul (fund ^ n))
  | inr h2 =>
    use (n+1)
    calc
    _ = u * 1 := by rw [_root_.mul_one u]
    _ = u * (fund ^ (-n) * fund ^ n) := by rw[fund_pow_cancel n]
    _ = u * fund ^ (-n) * fund ^ n := by rw[← _root_.mul_assoc]
    _ = A * fund ^ n := by exact rfl
    _ = fund * fund ^ n := by rw[h2]
    _ = _ := by exact (fund_mul_pow n)


-- Section 3: Tricks with mod

-- 3.1 fund³ ≡ 1 mod 3

lemma fund_cube_mod_3 : ∃ k : R, fund ^ (3 : ℤ) = 3 * k + 1 :=
by
  use ⟨6, 5, 4⟩
  simp only [fund, Nat.cast_one, α]
  ext <;>
  · ring_nf; rfl

-- 3.2 If fundⁿ = x-yα then n is congruent to 0 or -1 mod 3

-- 3.2.1 Lemmas

lemma fund_inv_cube_mod_3 : ∃ k : R, fund ^ (-3 : ℤ) = 3 * k + 1 :=
by
  use ⟨0, 1, -1⟩
  simp only [fund, Nat.cast_one, α]
  ext <;>
  · ring_nf; rfl

lemma fund_pow_three_n_pos (n : ℕ) : ∃ k : R, fund ^ (3 * n : ℤ) = 1 + 3 * k :=
by
  induction n with
  | zero => use 0; simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨v, hv⟩ := fund_cube_mod_3
    use k + v + 3 * k * v
    push_cast
    rw [mul_add, Int.mul_one, zpow_add]
    push_cast
    rw [hk, hv]
    ring

lemma fund_pow_three_n_neg (n : ℕ) : ∃ k : R, (fund ^ (- (3 * n):ℤ)) = 1 + 3 * k :=
by
  induction n with
  | zero => use 0; simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨v, hv⟩ := fund_inv_cube_mod_3
    use k + v + 3 * k * v
    push_cast
    rw [mul_add, Int.mul_one, neg_add, zpow_add]
    push_cast
    rw [hk, hv]
    ring

lemma fund_pow_three_n (n : ℤ) : ∃ k : R, fund ^ (3 * n) = 1 + 3 * k :=
by
  cases n with
  | ofNat n =>
    exact fund_pow_three_n_pos n
  | negSucc n =>
    rw [Int.negSucc_eq]
    have h := fund_pow_three_n_neg (n+1)
    norm_cast

lemma computation (v : R) :
    ((1 : R) + (3 : R) * v) * fund =
      ((1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z) +
      α * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z) +
      α ^ 2 * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z) :=
by
  have threex: (3:R).x = 3 := rfl
  have threey: (3:R).y = 0 := rfl
  have threez: (3:R).z = 0 := rfl
  have sixx: (6:R).x = 6 := rfl
  have sixy: (6:R).y = 0 := rfl
  have sixz: (6:R).z = 0 := rfl
  have h : (1 : R) + (3 : R) * v = ⟨1 + 3 * v.x, 3 * v.y, 3 * v.z⟩ := by
    ext <;>
    · simp only [one_def, mul_def, add_def, _root_.zero_add, add_right_inj, threex, threey, threez]
      ring
  have h2 :
      ((1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z) +
          α * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z) +
          α ^ 2 * ((1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z) =
        ⟨
          (1 : ℤ) + (3 : ℤ) * v.x + (6 : ℤ) * v.y + (6 : ℤ) * v.z,
          (1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (6 : ℤ) * v.z,
          (1 : ℤ) + (3 : ℤ) * v.x + (3 : ℤ) * v.y + (3 : ℤ) * v.z
        ⟩ := by
    ext <;>
    · simp only [
        Int.cast_one, one_def, Int_Cast_R, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        MulZeroClass.zero_mul, add_def, α, _root_.mul_one, _root_.one_mul, _root_.zero_add, sq
      ]
  rw [h, h2]
  ext <;>
  · simp only [mul_def]
    rw [fundx, fundy, fundz]
    ring

-- 3.2.2 The theorem

lemma fund_pow_n_mod_three (x : ℤ) (y : ℤ) (n : ℤ)
    (h : fund ^ n = (x : R) + (-y : R) * α) :
    (∃ k : ℤ, n = 3 * k) ∨ (∃ k : ℤ, n = 3 * k - 1) :=
by
  have nmod3: n % 3 =0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have upper : n % 3 < 3 := by
      refine Int.emod_lt_of_pos n ?upper.H
      decide
    have lower : n % 3 ≥ 0 := by
      refine Int.emod_nonneg n ?lower.a
      exact three_ne_zero
    have hk : ((Int.toNat (n % 3) : ℤ)) = n % 3 := by
      exact Int.toNat_of_nonneg lower
    have hk_lt : Int.toNat (n % 3) < 3 := by
      rw [Int.toNat_lt lower]
      exact upper
    cases hmod : Int.toNat (n % 3) with
    | zero =>
      left
      rw [hmod] at hk
      norm_num at hk
      exact hk.symm
    | succ k =>
      cases k with
      | zero =>
        right
        left
        rw [hmod] at hk
        norm_num at hk
        exact hk.symm
      | succ k =>
        cases k with
        | zero =>
          right
          right
          rw [hmod] at hk
          norm_num at hk
          exact hk.symm
        | succ k =>
          exfalso
          rw [hmod] at hk_lt
          have hk_ge : 3 ≤ k + 1 + 1 + 1 := by
            simp [Nat.add_left_comm, Nat.add_comm]
          exact (Nat.not_lt.mpr hk_ge) hk_lt
  have neqmod3 := (Int.mul_ediv_add_emod n 3).symm
  have nadd1eqmod3 := (Int.mul_ediv_add_emod (n + 1) 3).symm
  cases nmod3 with
  | inl h0 =>
    left
    use n / 3
    nth_rewrite 1 [neqmod3]
    rw [h0]
    norm_num
  | inr nmod3 =>
    cases nmod3 with
    | inl h1 =>
      set p:= n / 3 with hp
      have neq: n = 3 * p + 1 := by
        rw [← h1]
        exact neqmod3
      rw [neq] at h
      have fundpow: fund ^ (3 * p + 1) = fund ^ (3 * p) * fund := by
        rw [zpow_add fund (3 * p) 1, zpow_one, zpow_mul fund 3 p]
      have hcast: fund ^ (3:ℤ) = fund ^ (3:ℕ) := by
        exact rfl
      rw [fundpow] at h
      exfalso
      obtain ⟨v, hv⟩ := fund_pow_three_n p
      push_cast at h
      rw [hv] at h
      have contra := computation v
      rw [contra] at h
      have h' := zcompeq h
      have hz := zcomp x (-y) 0
      have hz2 := zcomp' (1+3*v.x+6*v.y+6*v.z) (1+3*v.x+3*v.y+6*v.z) (1+3*v.x+3*v.y+3*v.z)
      have heq1: x + (-y:ℤ) * α + 0 * α ^ 2 = x + (-y) * α := by
        norm_cast
        ring
      have h'' := zcompeq heq1
      push_cast at hz
      rw [zero_mul, add_zero] at hz
      rw [hz] at h'
      push_cast at hz2
      push_cast at h'
      rw [hz2] at h'
      have threemuladd: 1 + 3 * v.x + 3 * v.y + 3 * v.z = 1 + 3 * (v.x + v.y + v.z) := by
        ring
      rw [threemuladd] at h'
      have contra2: 3 * (v.x + v.y + v.z) = -1 := by
        calc
        _ = 1 + 3 * (v.x + v.y + v.z) - 1 := by ring
        _ = 0 - 1 := by rw[h']
        _ = _ := by ring
      have neg := Int.eq_one_or_neg_one_of_mul_eq_neg_one' contra2
      cases neg with
      | inl neg =>
        obtain ⟨c, _⟩ := neg
        contradiction
      | inr neg =>
        obtain ⟨c, _⟩ := neg
        contradiction
    | inr h2 =>
      right
      use (n + 1) / 3
      have h': (n + 1) % 3 = 0 := by
        simp only [EuclideanDomain.mod_eq_zero]
        use (n / 3 + 1)
        rw[mul_add]
        nth_rewrite 1 [neqmod3]
        rw [h2]
        ring
      rw [h'] at nadd1eqmod3
      norm_num at nadd1eqmod3
      rw [← nadd1eqmod3]
      ring

-- 3.3 For all natural numbers n≥1 we have u⁽³ⁿ⁾ ≡ 1 + 3ⁿ(α²-α) mod 3ⁿ⁺¹

lemma cubic_expansion : (1 + a)^3 = 1 + 3 * a + 3 * a ^ 2 + a ^ 3 :=
by
  ring

lemma mod_prop (h1 : ∃ a', a = c * a') (h2 : ∃ b', b = c * b') : ∃ k, a + b = c * k :=
by
  obtain ⟨a', ha'⟩ := h1
  obtain ⟨b', hb'⟩ := h2
  use (a'+b')
  rw[ha', hb']
  ring

lemma mod_prop2 (n : ℕ) (h : 1 ≤ n) : ∃ k, 3 * (3 ^ n * a) ^ 2 = 3 ^ (n + 2) * k :=
by
  use (3^(n-1) * a ^2)
  push_cast
  rw [mul_pow]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← pow_mul]
  have : (3:R) = (3:R) ^ 1 := by rw [pow_one]
  nth_rewrite 1 [this]
  rw [← pow_add, ← pow_add]
  congr 1
  rw [Nat.add_comm]
  nth_rewrite 2 [Nat.add_comm]
  rw [← Nat.add_assoc, add_left_inj]
  nth_rewrite 2 [Nat.add_comm]
  rw [Nat.add_assoc, Nat.sub_add_cancel h]
  ring

lemma mod_prop3 (n : ℕ) (h : 1 ≤ n) : ∃ k, (3 ^ n * a) ^ 3 = 3 ^ (n + 2) * k :=
by
  use (3 ^ (2 * n - 2) * a ^ 3)
  push_cast
  rw [mul_pow, ← pow_mul, ← mul_assoc]
  congr 1
  rw [← pow_add]
  congr 1
  have : 2 ≤ 2 * n := by simp only [Nat.ofNat_pos, le_mul_iff_one_le_right, h]
  rw [Nat.add_assoc, Nat.add_sub_cancel' this]
  ring

lemma fund_pow_three_pow_n (n : ℕ) (h : 1 ≤ n) :
    ∃ k : R,
      (fund ^ (3 ^ n) : R) = (3 : ℕ) ^ (n + 1) * (k : R) + (1 : ℕ) + (3 : ℕ) ^ n * (α ^ 2 - α) :=
by
  set m:= n - 1 with hm
  have hn: n = m + 1 := by
    calc
    _ = n - 1 + 1 := by exact (Nat.sub_add_cancel h).symm
    _ = _ := by rw [hm]
  rw [hn]
  induction m with
  | zero =>
    use ⟨2, 2, 1⟩
    simp only [Nat.zero_add, one_add_one_eq_two, pow_one, sq]
    simp only [fund, Nat.cast_one, α, pow_three, Units.val_mul, sq]
    ext <;>
    · ring_nf; rfl
  | succ m' ih =>
    set n':= m' + 1 with hn'
    obtain ⟨k, hk⟩ := ih
    rw [pow_add, pow_one, pow_mul]
    push_cast
    have hkcast: (fund ^ 3 ^ n':R) = ((fund:R) ^ 3 ^ n') := by
      norm_cast
    rw [hkcast] at hk
    have hkrw :
        ↑(3 ^ (n' + 1)) * k + ↑1 + ↑(3 ^ n') * (α ^ 2 - α) =
          ↑1 + ↑(3 ^ n') * (α ^ 2 - α + 3 * k) := by
      calc
      _ = 1 + ↑(3 ^ (n' + 1)) * k + ↑(3 ^ n') * (α ^ 2 - α) := by
        congr 1
        rw [add_comm]
        push_cast
        rfl
      _ = _ := by
        rw [add_assoc]
        congr
        push_cast
        rw [pow_add, pow_one]
        nth_rewrite 1 [mul_assoc]
        rw [add_comm, mul_add]
    push_cast at hk
    push_cast at hkrw
    rw [hkrw] at hk
    rw [hk]
    have hn'1: 1 ≤ n' := by
      rw [hn']
      exact Nat.le_add_left 1 m'
    have hm'1: 1 + m' - 1 = m' := by
      calc
      _ = m' + 1 - 1 := by ring_nf
      _ = _ := by exact rfl
    clear hkcast hkrw
    rw [cubic_expansion]
    have h1: ∃ x, 3 ^ (n' + 2) * k = 3 ^ (n' + 2) * x := by
      use k
    have h2: ∃ y, 3 * (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 2 = 3 ^ (n' + 2) * y := by
      exact (mod_prop2 (α ^ 2 - α + 3 * k) n' hn'1)
    have h3: ∃ z, (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 3 = 3 ^ (n' + 2) * z := by
      exact (mod_prop3 (α ^ 2 - α + 3 * k) n' hn'1)
    have h4 := mod_prop
      (3 ^ (n' + 2) * k)
      (3 * (3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 2)
      (3 ^ (n' + 2)) h1 h2
    have h5 := mod_prop
      (↑(3 ^ (n' + 2)) * k + ↑3 * (↑(3 ^ n') * (α ^ 2 - α + 3 * k)) ^ 2)
      ((3 ^ n' * (α ^ 2 - α + 3 * k)) ^ 3)
      (3 ^ (n' + 2)) h4 h3
    obtain ⟨k1, hk1⟩ := h5
    push_cast at hk1
    use k1
    have : n' + 1 + 1 = n' + 2 := by ring
    rw [this]
    clear this
    rw [←hk1]
    push_cast
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

theorem pow_pos (a : ℕ) (n : ℕ) (h : 0 < a) : 0 < a ^ n :=
by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [pow_succ]
    apply mul_pos
    · exact ih
    · exact h

lemma ceil_prop (x : ℝ) (y : ℝ) (h : 0 < y) : x ≤ y * Nat.ceil (x / y) :=
by
  have nonzero: y ≠ 0 := by
    exact ne_of_gt h
  have h0: x / y ≤ Nat.ceil (x / y) := by
    exact Nat.le_ceil (x / y)
  calc
  _ = x / y * y := by exact (div_eq_iff nonzero).mp rfl
  _ ≤ Nat.ceil (x / y) * y := by exact mul_le_mul_of_nonneg_right h0 h.le
  _ = _ := by ring

lemma log_three (x : ℤ) (h : 0 ≤ x) : ∃ r : ℕ, x < 3 ^ r :=
by
  by_cases eqzero: x = 0
  · use 1
    rw[eqzero]
    norm_num
  · have nonzero: 0 ≠ x := by
      intro hx0
      exact eqzero hx0.symm
    have hpos: 0 < x := by
      exact Ne.lt_of_le nonzero h
    use Nat.ceil (Real.log x / Real.log 3) + 1
    have hpos': 0 < (x:ℝ) := by
      norm_cast
    have hlog3pos: 0 < Real.log 3 := by
      have h13: (1:ℝ) < 3 := by
        norm_num
      exact Real.log_pos h13
    have hleq: x ≤ 3 ^ Nat.ceil (Real.log x / Real.log 3) := by
      have explog1: x = Real.exp (Real.log x) := by
        exact (Real.exp_log hpos').symm
      have ceil_prop := ceil_prop (Real.log x) (Real.log 3) hlog3pos
      rw [← Real.exp_le_exp] at ceil_prop
      rw [← explog1] at ceil_prop
      rw [Real.exp_mul] at ceil_prop
      rw [Real.exp_log three_pos] at ceil_prop
      norm_cast at ceil_prop
    push_cast at hleq
    have hpos2: (0:ℕ) < 3 ^ ⌈Real.log x / Real.log 3⌉₊ := by
      exact pow_pos 3 ⌈Real.log x / Real.log 3⌉₊ three_pos
    have h13: (1:ℕ) < 3 := by
      exact Nat.one_lt_succ_succ 1
    calc
    x ≤ 3 ^ Nat.ceil (Real.log x / Real.log 3) := by push_cast; exact hleq
    _ < 3 ^ Nat.ceil (Real.log x / Real.log 3) * 3 := by norm_cast; exact lt_mul_right hpos2 h13

lemma mul_nonneg_iff_pos_imp_nonneg (a : ℤ) (b : ℤ) :
    0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

lemma mul_nonpos_iff_pos_imp_nonpos (a : ℤ) (b : ℤ) :
    a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma eq_zero_of_div_by_gt (x : ℤ) (y : ℤ) (hx : 0 ≤ x) (_hy : 0 < y)
    (h1 : y ∣ x) (h2 : x < y) : x = 0 :=
by
  exact Int.eq_zero_of_dvd_of_nonneg_of_lt hx h2 h1

lemma eq_zero_of_div_by_gt2 (x : ℤ) (y : ℤ) (hx : x ≤ 0) (_hy : y < 0)
    (h1 : y ∣ x) (h2 : y < x) : x = 0 :=
by
  have hx' : 0 ≤ -x := by
    linarith
  have h1' : (-y) ∣ (-x) := by
    obtain ⟨k, hk⟩ := h1
    use k
    linarith
  have h2' : -x < -y := by
    linarith
  have hzero : -x = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hx' h2' h1'
  linarith

-- 3.4.2 If uⁿ = x-yα and n is congruent to 0 modulo 3, then n = 0.

lemma mod_three_pow_imp_zero (x : ℤ) (h : ∀ (r : ℕ), x % 3 ^ r = 0) : x = 0 :=
by
  norm_cast at h
  by_cases sign: 0 ≤ x
  · obtain ⟨r, hr⟩ := log_three x sign
    specialize h r
    have powpos: (0:ℤ) < 3 ^ r := by
      exact_mod_cast pow_pos 3 r three_pos
    have div: (3 ^ r:ℤ) ∣ x := by
      use x / (3 ^ r)
      have hdiv := Int.mul_ediv_add_emod x (3 ^ r)
      rw [h] at hdiv
      nth_rewrite 1 [← hdiv]
      norm_num
    exact eq_zero_of_div_by_gt x (3 ^ r) sign powpos div hr
  · push Not at sign
    have sign' := le_of_lt sign
    have sign2 : 0 ≤ -x := by
      rw [le_neg]
      exact sign'
    obtain ⟨r, hr⟩ := log_three (-x) sign2
    rw [neg_lt] at hr
    specialize h r
    have powneg: -3 ^ r < (0:ℤ) := by
      have powpos : (0 : ℤ) < 3 ^ r := by
        exact_mod_cast pow_pos 3 r three_pos
      linarith
    have div: (-3 ^ r:ℤ) ∣ x := by
      use x / (-3 ^ r)
      have hdiv := Int.mul_ediv_add_emod x (-3 ^ r)
      rw [← Int.emod_neg] at h
      rw [h] at hdiv
      nth_rewrite 1 [← hdiv]
      norm_num
    have h' := eq_zero_of_div_by_gt2 x (-3 ^ r) sign' powneg div hr
    rw [h'] at sign
    contradiction

lemma zcomp_of_sum : (a+b).z = a.z+b.z :=
by
  exact rfl

lemma zcomp_of_scalar_mul (d : ℤ) : (d * a).z = d * a.z :=
by
  simp only [Int_Cast_R, mul_def, MulZeroClass.mul_zero, MulZeroClass.zero_mul, _root_.add_zero]

lemma mod_prop4 (d : ℤ) (h : ∃ k, a = d * k + b) : ∃ v, a.z = d * v + b.z :=
by
  obtain ⟨k, hk⟩ := h
  use k.z
  rw [hk]
  rw[zcomp_of_sum, zcomp_of_scalar_mul]

lemma pre1_final_case_one (b r : ℕ) (h : 1 ≤ r) :
    ∃ x, ↑((fund ^ 3 ^ r) ^ b) = ↑(3 ^ (r + 1)) * x + (1 + ↑(3 ^ r * b) * (α ^ 2 - α)) :=
by
  induction b with
  | zero => use 0; simp only [fund, Nat.cast_one, α, pow_zero, Units.val_one, Nat.cast_pow,
    Nat.cast_ofNat, MulZeroClass.mul_zero, Nat.cast_zero, MulZeroClass.zero_mul, _root_.add_zero,
    _root_.zero_add]
  | succ n h =>
    obtain ⟨k, hk⟩ := h
    obtain ⟨v, hv⟩ := fund_pow_three_pow_n r h
    nth_rewrite 1 [pow_add]
    rw [pow_one]
    have : ((fund ^ 3 ^ r) ^ n * fund ^ 3 ^ r :Rˣ) = ((fund ^ 3 ^ r) ^ n * (fund ^ 3 ^ r: R)) := by
      norm_cast
    rw [this, hk, hv]
    clear this hk hv
    simp only [add_mul, mul_add, one_mul, Nat.cast_one, Nat.mul_one]
    push_cast
    simp only [add_mul, mul_one, ← add_assoc]
    nth_rewrite 1 [add_comm]
    simp only [← add_assoc]
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
    simp only [mul_add]
    push_cast
    congr 2
    · congr 2
      · congr 1
        · simp only [← mul_assoc]
        · simp only [← mul_assoc]
          congr 1
          rw [mul_comm]
          simp only [← mul_assoc]
          congr 2
          simp only [← pow_add]
          congr 1
          rw [Nat.add_assoc]
          congr
          rw [Nat.add_comm]
          exact (Nat.sub_add_cancel h).symm
      · simp only [← mul_assoc]
    · simp only [← mul_assoc]
      congr 1
      ring

lemma neg_int_eq_nat (a : ℤ) (h : a < 0) : ∃ b : ℕ, a = -b := by
  have : 0 ≤ -a := by
    simp only [Left.nonneg_neg_iff]
    exact Int.le_of_lt h
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le this
  use b
  rw [← hb]
  simp only [neg_neg]

lemma pow_neg_one_eq_inv (u : Rˣ) : u ^ (-1 : ℤ) = u⁻¹ :=
by
  simp only [Int.reduceNeg, zpow_neg, zpow_one]

lemma both_mul (a b : R) (u : Rˣ) : a = b → u * a = u * b :=
by
  intro h
  congr

lemma find_inv (u : Rˣ) (v : R) : u * v = 1 → u⁻¹ = v :=
by
  intro h
  have := both_mul (u * v) 1 u⁻¹ h
  rw [← mul_assoc] at this
  norm_cast at this
  simp at this
  exact this.symm

lemma inv_mod (u : Rˣ) (v k : R) (h : u * v = (1 : R) + (3 : R) ^ (r + 1) * k) :
    ∃ d : R, u⁻¹ = (3 : R) ^ (r + 1) * d + v :=
by
  use -u⁻¹ * k
  apply find_inv
  simp only [mul_add]
  rw [h]
  ring_nf
  have : (u:R) * u⁻¹ = 1 := by simp only [Units.mul_inv]
  rw [this]
  ring

lemma pre_pre_2_final_case_one (r : ℕ) (h : 1 ≤ r) :
    ∃ v : R,
      (fund ^ 3 ^ r) ^ (-1 : ℤ) = (3 : R) ^ (r + 1) * v + ((1 : R) - (3 : R) ^ r * (α ^ 2 - α)) :=
by
  rw [pow_neg_one_eq_inv]
  obtain ⟨k, hk⟩ := fund_pow_three_pow_n r h
  have h0 :
      (fund ^ 3 ^ r) * ((1 : R) - (3 : R) ^ r * (α ^ 2 - α)) =
        (1 : R) + (3 : R) ^ (r + 1) *
          (k - (3 : R) ^ r * k * (α ^ 2 - α) - (3 : R) ^ (r - 1) * (α ^ 2 - α) * (α ^ 2 - α)) := by
    rw [hk]
    push_cast
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
      simp only [← pow_add]
      congr 1
      nth_rw 2 [Nat.add_comm]
      rw [Nat.add_assoc]
      congr
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel h).symm
  exact inv_mod
    (fund ^ 3 ^ r)
    ((1 : R) - (3 : R) ^ r * (α ^ 2 - α))
    (k - (3 : R) ^ r * k * (α ^ 2 - α) - (3 : R) ^ (r - 1) * (α ^ 2 - α) * (α ^ 2 - α))
    h0

lemma pre_2_final_case_one (b r : ℕ) (h : 1 ≤ r) :
    ∃ x : R,
      ((fund ^ 3 ^ r) ^ (-1 : ℤ)) ^ b =
        (3 : R) ^ (r + 1) * x + ((1 : R) + (3 : R) ^ r * -↑b * (α ^ 2 - α)) :=
by
  push_cast
  induction b with
  | zero => use 0; simp only [fund, Nat.cast_one, α, Int.reduceNeg, zpow_neg, zpow_one, pow_zero,
    MulZeroClass.mul_zero, Nat.cast_zero, neg_zero, MulZeroClass.zero_mul, _root_.add_zero,
    _root_.zero_add]
  | succ n h =>
    obtain ⟨k, hk⟩ := h
    obtain ⟨v, hv⟩ := pre_pre_2_final_case_one r h
    nth_rewrite 1 [pow_add]
    rw [pow_one]
    rw [hk, hv]
    clear hk hv
    push_cast
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
              simp only [← pow_add]
              congr 1
              rw [Nat.add_assoc]
              congr
              rw [Nat.add_comm]
              exact (Nat.sub_add_cancel h).symm
          · push_cast; ring
        · push_cast; ring
      · push_cast; ring
    · ring

lemma important (r : ℕ) (a : ℤ) (rpos : 1 ≤ r) :
    ∃ x, ↑((fund ^ (3 : ℤ) ^ r) ^ a) = ↑(3 ^ (r + 1)) * x +
      (↑(1 : ℕ) + ↑(3 ^ r) * ↑a * (α ^ 2 - α)) :=
by
  obtain ⟨k, hk⟩ := fund_pow_three_pow_n r rpos
  by_cases apos : 0 ≤ a
  · obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le apos
    rw [hb]
    norm_cast
    exact pre1_final_case_one b r rpos
  · push Not at apos
    obtain ⟨b, hb⟩ := neg_int_eq_nat a apos
    rw [hb]
    nth_rw 1 [← Int.mul_neg_one]
    nth_rw 1 [Int.mul_comm]
    rw [zpow_mul]
    norm_cast
    simp only [Int.reduceNegSucc, Int.reduceNeg]
    push_cast
    exact pre_2_final_case_one b r rpos

theorem final_case_one (x : ℤ) (y : ℤ) (n : ℤ)
    (h1 : fund ^ n = (x : R) + (-y : R) * α) (h2 : ∃ k : ℤ, n = 3 * k) : n = 0 :=
by
  have h: ∀ (r:ℕ), n % 3 ^ r = 0 := by
    intro r
    induction r with
    | zero =>
      rw [pow_zero]
      norm_num
    | succ r ih =>
      by_cases rpos: 1 ≤ r
      · set a := n / ((3:ℤ) ^ r) with ha
        have hdiv := Int.mul_ediv_add_emod n (3 ^ r)
        rw [ih] at hdiv
        norm_num at hdiv
        rw [← ha] at hdiv
        have hdiv': a%3=0 → n % ↑(3 ^ (r + 1)) = 0 := by
          intro h
          norm_num at h
          obtain ⟨k, hk⟩ := h
          norm_num
          use k
          rw [pow_add, pow_one, Int.mul_assoc]
          rw [← hk]
          exact hdiv.symm
        apply hdiv'
        norm_num
        have preh0: ∃ x, (fund^n).val = 3 ^ (r+1) * x + (1 + 3 ^ r * a * (α^2 - α)) := by
          rw [← hdiv, zpow_mul]
          exact important r a rpos
        have h0: ∃(v:ℤ),((fund^n).val).z =3 ^ (r+1) * v + 3 ^ r * a := by
          have h0' := mod_prop4 (fund^n).val (1 + 3 ^ r * a * (α^2 - α)) (3 ^ (r+1)) preh0
          obtain ⟨v, hv⟩ := h0'
          use v
          rw [hv]
          congr
          rw [zcomp_of_sum]
          have : α ^ 2 - α = α ^ 2 + (-α) := by
            ring
          rw [this, mul_add, zcomp_of_sum]
          clear this
          have h1: (↑(1:ℕ):R).z = 0 := by
            rfl
          have h2: (↑(3 ^ r) * ↑a * α ^ 2).z = ↑(3 ^ r) * a := by
            norm_cast
            rw [zcomp_of_scalar_mul]
            have : (α ^ 2).z = 1 := by
              rfl
            rw [this]
            ring
          have h3: (↑(3 ^ r) * ↑a * -α).z = 0 := by
            norm_cast
            rw [zcomp_of_scalar_mul]
            have : (-α).z = 0 := by
              rfl
            rw [this]
            ring
          rw [h1, h2, h3]
          ring
        obtain ⟨v, hv⟩ := h0
        use (-v)
        rw [h1] at hv
        have hz:= zcomp x (-y) 0
        push_cast at hz
        rw [zero_mul, add_zero] at hz
        rw [hv] at hz
        push_cast at hz
        have ha': a * (3:ℤ) ^ r = (3:ℤ) * (-v) * (3:ℤ) ^ r := by
          calc
          _ = (3:ℤ) ^ (r + 1) * v + (3:ℤ) ^ r * a - (3:ℤ) ^ (r + 1) * v := by ring
          _ = (0:ℤ) - (3:ℤ) ^ (r + 1) * v := by rw [hz]
          _ = (-v) * (3:ℤ) ^ (r + 1) := by ring
          _ = _ := by rw[pow_add]; ring
        have nonzero: (3:ℤ) ^ r ≠ 0 := by
          exact pow_ne_zero r three_ne_zero
        rw [mul_eq_mul_right_iff] at ha'
        cases ha' with
        | inl ha' =>
          exact ha'
        | inr ha' =>
          rw [ha'] at nonzero
          contradiction
      · push Not at rpos
        rw [Nat.lt_one_iff] at rpos
        rw [rpos]
        ring_nf
        obtain ⟨k, hk⟩ := h2
        rw [hk]
        simp only [Int.mul_emod_right]
  exact mod_three_pow_imp_zero n h

-- 3.4.3 If uⁿ = x-yα and n is congruent to -1 modulo 3, then n = -1.

theorem final_case_two (x : ℤ) (y : ℤ) (n : ℤ)
    (h1 : fund ^ n = (x : R) + (-y : R) * α) (h2 : ∃ k : ℤ, n = 3 * k - 1) : n = -1 :=
by
  have h: ∀ (r:ℕ), (n + 1) % 3 ^ r = 0 := by
    intro r
    induction r with
    | zero =>
      rw [pow_zero]
      norm_num
    | succ r ih =>
      by_cases rpos: 1 ≤ r
      · set a := (n + 1) / ((3:ℤ) ^ r) with ha
        have hdiv := Int.mul_ediv_add_emod (n + 1) ((3 : ℤ) ^ r)
        have ih' : (n + 1) % ((3 : ℤ) ^ r) = 0 := by simpa using ih
        rw [ih'] at hdiv
        norm_num at hdiv
        rw [← ha] at hdiv
        have hdiv': a%3=0 → (n + (1:ℕ)) % ↑(3 ^ (r + 1)) = 0 := by
          intro h
          norm_num at h
          obtain ⟨k, hk⟩ := h
          norm_num
          use k
          rw [pow_add, pow_one, Int.mul_assoc]
          rw [← hk]
          exact hdiv.symm
        apply hdiv'
        norm_num
        have preh0 :
            ∃ x,
              (fund ^ n).val =
                3 ^ (r + 1) * x +
                  (α + 3 ^ r * a * (2 - α ^ 2) - (1 + 3 ^ r * a * (α ^ 2 - α))) := by
          have hn: n = (3:ℤ) ^ r * a - 1 := by
            rw [hdiv]
            ring
          rw [hn]
          nth_rw 1 [sub_eq_add_neg]
          rw [zpow_add]
          push_cast
          rw [fund_inv]
          rw [zpow_mul]
          obtain ⟨k, hk⟩ := important r a rpos
          rw [hk]
          use (-k + k*α)
          nth_rw 2 [sub_eq_add_neg]
          nth_rw 3 [← mul_neg_one]
          simp only [mul_add, add_mul, ← add_assoc]
          push_cast
          simp only [one_mul]
          nth_rw 1 [add_assoc]
          nth_rw 1 [add_assoc]
          nth_rw 1 [add_comm]
          simp only [← add_assoc]
          congr 2
          nth_rw 1 [add_comm]
          simp only [← add_assoc]
          congr 1
          · ring
          · nth_rw 1 [mul_assoc]
            congr
        have h0: ∃(v:ℤ),((fund^n).val).z = 3 ^ (r+1) * v + (-2) * 3 ^ r * a := by
          have h0' := mod_prop4
            (fund ^ n).val
            (α + 3 ^ r * a * (2 - α ^ 2) - (1 + 3 ^ r * a * (α ^ 2 - α)))
            (3 ^ (r + 1)) preh0
          obtain ⟨v, hv⟩ := h0'
          use v
          rw [hv]
          congr
          simp only [sub_eq_add_neg, zcomp_of_sum]
          have h1: α.z = 0 := rfl
          have h2: (↑(3 ^ r) * ↑a * ((2:ℕ) + -α ^ 2)).z = - (3^r)*a := by
            norm_cast
            rw [zcomp_of_scalar_mul, zcomp_of_sum, mul_add]
            have : z 2 = 0 := rfl
            rw [this]; clear this
            ring_nf
            have : (-α ^ 2).z = -1 := by congr
            rw [this]
            ring
          have h3: (-((1:ℕ) + ↑(3 ^ r) * ↑a * (α ^ 2 + -α))).z = - (3^r)*a := by
            rw [← neg_one_mul, mul_add, zcomp_of_sum]
            rw [mul_add, mul_add, zcomp_of_sum, ← Int.add_assoc]
            have h01: (-(1:R) * (1:ℕ)).z = 0 := rfl
            have h02: (-(1:R) * (↑(3 ^ r) * ↑a * α ^ 2)).z = - (3^r)*a := by
              nth_rw 1 [mul_comm]
              norm_cast
              simp only [Int.reduceNegSucc, Int.reduceNeg]
              rw [mul_assoc, zcomp_of_scalar_mul]
              nth_rw 1 [mul_comm]
              rw [zcomp_of_scalar_mul]
              have : (α ^ 2).z = 1 := by congr
              rw [this]
              ring
            have h03: (-1 * (↑(3 ^ r) * ↑a * -α)).z = 0 := by
              nth_rw 1 [mul_comm]
              norm_cast
              simp only [Int.reduceNegSucc, Int.reduceNeg]
              rw [mul_assoc, zcomp_of_scalar_mul]
              nth_rw 1 [mul_comm]
              rw [zcomp_of_scalar_mul]
              have : (-α).z = 0 := by congr
              rw [this]
              ring
            rw [h01, h02, h03]
            ring
          rw [h1, h2, h3]
          ring
        obtain ⟨v, hv⟩ := h0
        rw [h1] at hv
        have hz:= zcomp x (-y) 0
        push_cast at hz
        rw [zero_mul, add_zero] at hz
        rw [hv] at hz
        push_cast at hz
        have comp :
            (3 : ℤ) ^ (r + 1) * v + (-2 : ℤ) * (3 : ℤ) ^ r * a =
              ((3 : ℤ) * v - (2 : ℤ) * a) * (3 : ℤ) ^ r := by
          calc
          _ = (3:ℤ) ^ r * (3:ℤ) * v + (3:ℤ) ^ r * ((-2:ℤ) * a) := by rw [pow_add]; ring
          _ = (3:ℤ) ^ r * ((3:ℤ) * v + ((-2:ℤ) * a)) := by rw[Int.mul_assoc, ← mul_add]
          _ = _ := by ring
        rw [comp] at hz
        rw [Int.mul_eq_zero] at hz
        have eqzero: 3 * v = 2 * a := by
          cases hz with
          | inl hz =>
            calc
            _ = 3 * v - 2 * a + 2 * a := by ring
            _ = 0 + 2 * a := by rw [hz]
            _ = _ := by ring
          | inr hz =>
            have nonzero: (3:ℤ) ^ r ≠ 0 := by
              exact pow_ne_zero r three_ne_zero
            contradiction
        have dvd := dvd_mul_left 3 v
        rw [Int.mul_comm] at dvd
        rw [eqzero] at dvd
        have hgcd : Int.gcd 3 2 = 1 := by
          decide
        exact Int.dvd_of_dvd_mul_right_of_gcd_one dvd hgcd
      · push Not at rpos
        rw [Nat.lt_one_iff] at rpos
        rw [rpos]
        ring_nf
        obtain ⟨k, hk⟩ := h2
        rw [hk]
        ring_nf
        simp only [Int.mul_emod_left]
  have h2:= mod_three_pow_imp_zero (n+1) h
  calc
  _ = n + 1 - 1 := by ring
  _ = 0 - 1 := by rw [h2]
  _ = _ := by ring


-- Section 4: Conclusion

-- 4.1 Equivalence of the problem

theorem norm_one_iff (x y : ℤ) :
    (∃ u : Rˣ, norm u = 1 ∧ x + (-y) * α = u) ↔ x ^ 3 - 2 * y ^ 3 = 1 :=
by
  constructor
  · intro h
    obtain ⟨u, h1, h2⟩ := h
    have hux: (u.val).x = x := by
      rw[← h2]
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have huy: (u.val).y=-y := by
      rw[← h2]
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have huz: (u.val).z = 0 := by
      rw[← h2]
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have hnorm: norm u = x ^ 3 - 2 * y ^ 3 := by
      simp only [norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, hux, huy, huz]
      ring
    rw[hnorm] at h1
    exact h1
  · intro h
    set u:R := ⟨x, -y, 0⟩ with hu
    have hux: u.x = x := by
      rw [hu]
    have huy: u.y = -y := by
      rw [hu]
    have huz: u.z = 0 := by
      rw [hu]
    have hnorm: norm u = 1 := by
      simp only [norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, hux, huy, huz]
      ring_nf
      rw[← h]
      ring
    have hunit:= unit_of_norm u hnorm
    obtain ⟨v, hv⟩ := hunit
    use v
    constructor
    · simp only [hv, norm, Nat.cast_ofNat, MonoidHom.coe_mk, OneHom.coe_mk, hux, huy, huz]
      ring_nf
      rw[← h]
      ring
    · rw[hv]
      ext
      · simp only [
          hux, α, Int_Cast_R, neg_def, neg_zero, mul_def, MulZeroClass.mul_zero,
          _root_.add_zero, _root_.mul_one, add_def, _root_.zero_add
        ]
      · simp only [
          huy, α, Int_Cast_R, neg_def, neg_zero, mul_def, MulZeroClass.mul_zero,
          _root_.add_zero, _root_.mul_one, add_def, _root_.zero_add
        ]
      · simp only [
          huz, α, Int_Cast_R, neg_def, neg_zero, mul_def, MulZeroClass.mul_zero,
          _root_.add_zero, _root_.mul_one, add_def, _root_.zero_add
        ]

-- 4.2 QED

theorem Thue (x y : ℤ) (h : x ^ 3 - 2 * y ^ 3 = 1) : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = -1) :=
by
  rw[← norm_one_iff] at h
  obtain ⟨u, h1, h2⟩ := h
  have h0:= unit_eq_fund_pow u h1
  obtain ⟨n, hn'⟩ := h0
  have hn: (u:R) = (fund ^ n:R) := by
    norm_cast
  rw [← h2] at hn
  have h':= fund_pow_n_mod_three x y n hn.symm
  cases h' with
  | inl h' =>
    left
    have hn0 := final_case_one x y n hn.symm h'
    rw[hn0] at hn
    have fundpow0: fund ^ (0:ℤ) = 1 := by
      exact rfl
    rw [fundpow0] at hn
    have hx' : (x + (-y) * α).x = x := by
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have hx : (x + (-y) * α).x = 1 := by
      rw [hn]
      rfl
    rw [hx'] at hx
    have hy' : (x + (-y) * α).y = -y := by
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have hy : (x + (-y) * α).y = 0 := by
      rw [hn]
      rfl
    rw [hy', neg_eq_zero] at hy
    constructor
    · exact hx
    · exact hy
  | inr h' =>
    right
    have hn0 := final_case_two x y n hn.symm h'
    rw [hn0] at hn
    rw [fund_inv] at hn
    have hx': (x + (-y) * α).x = x := by
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have hx: (x + (-y) * α).x = -1 := by
      rw[hn]
      rfl
    rw [hx'] at hx
    have hy': (x + (-y) * α).y = -y := by
      simp only [
        Int_Cast_R, neg_def, neg_zero, α, mul_def, MulZeroClass.mul_zero, _root_.add_zero,
        _root_.mul_one, add_def, _root_.zero_add
      ]
    have hy: (x + (-y) * α).y = 1 := by
      rw [hn]
      rfl
    rw [hy', neg_eq_iff_eq_neg] at hy
    constructor
    · exact hx
    · exact hy

end

end R
