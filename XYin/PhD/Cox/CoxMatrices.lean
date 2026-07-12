import Mathlib.NumberTheory.Cyclotomic.Basic
import XYin.PhD.Cox.HermiteNormalForm
import XYin.PhD.Cox.ModularFunction

/-!
# Cox representatives `C(m)`

The same triple `(a,b,d)` has two deliberately distinct matrices:

* the Möbius matrix `!![a,b;0,d]`, acting by `τ ↦ (aτ+b)/d`;
* the sublattice inclusion HNF `!![d,b;0,a]`, whose columns generate `[d,aτ+b]`.

The gcd condition is not part of HNF: it is the extra primitive condition equivalent to a
cyclic quotient.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

/-- Cox's finite set `C(m)` of primitive upper-triangular determinant-`m` matrices. -/
structure CoxMatrix (m : ℕ+) where
  a : ℕ
  b : ℕ
  d : ℕ
  a_pos : 0 < a
  determinant : a * d = (m : ℕ)
  b_lt : b < d
  primitive : Nat.gcd (Nat.gcd a b) d = 1

namespace CoxMatrix

variable {m : ℕ+}

theorem d_pos (σ : CoxMatrix m) : 0 < σ.d := by
  sorry

theorem a_le (σ : CoxMatrix m) : σ.a ≤ (m : ℕ) := by
  sorry

theorem d_le (σ : CoxMatrix m) : σ.d ≤ (m : ℕ) := by
  sorry

/-- Cox's matrix acting on the upper half-plane. -/
def mobiusMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.a : ℤ), (σ.b : ℤ); 0, (σ.d : ℤ)]

/-- The column-HNF inclusion matrix for the associated sublattice `[d,aτ+b]`. -/
def inclusionMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.d : ℤ), (σ.b : ℤ); 0, (σ.a : ℤ)]

theorem inclusionMatrix_isColumnHermiteNormalForm (σ : CoxMatrix m) :
    σ.inclusionMatrix.IsColumnHermiteNormalForm := by
  sorry

theorem inclusionMatrix_det (σ : CoxMatrix m) :
    σ.inclusionMatrix.det = (m : ℕ) := by
  sorry

theorem inclusionMatrix_content_eq_one (σ : CoxMatrix m) :
    Matrix.rankTwoContent σ.inclusionMatrix = 1 := by
  sorry

/-- The Möbius action `(aτ+b)/d`. -/
def act (σ : CoxMatrix m) (τ : ℍ) : ℍ :=
  ⟨((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ), by
    have hd : ((σ.d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr σ.d_pos.ne'
    have hd_pos : (0 : ℝ) < (σ.d : ℝ) := by exact_mod_cast σ.d_pos
    have ha : (0 : ℝ) < (σ.a : ℝ) := by exact_mod_cast σ.a_pos
    have him : (((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ)).im =
        (σ.a : ℝ) * (τ : ℂ).im / (σ.d : ℝ) := by
      rw [Complex.div_im, Complex.normSq_natCast]
      simp [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
        Complex.natCast_im, Complex.natCast_re]
      field_simp
    rw [him]
    exact div_pos (mul_pos ha τ.im_pos) hd_pos⟩

@[simp] theorem coe_act (σ : CoxMatrix m) (τ : ℍ) :
    ((σ.act τ : ℍ) : ℂ) =
      ((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ) := rfl

/-- A bounded encoding used to obtain the finite type structure on `C(m)`. -/
def toFin (σ : CoxMatrix m) :
    Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) :=
  (⟨σ.a, by have := σ.a_le; omega⟩,
   ⟨σ.b, by have := σ.b_lt; have := σ.d_le; omega⟩,
   ⟨σ.d, by have := σ.d_le; omega⟩)

theorem toFin_injective : Function.Injective (toFin (m := m)) := by
  sorry

instance : DecidableEq (CoxMatrix m) := fun x y ↦
  decidable_of_iff (x.toFin = y.toFin) toFin_injective.eq_iff

instance : Fintype (CoxMatrix m) := Fintype.ofInjective toFin toFin_injective

end CoxMatrix

/-- Right cosets of `Γ₀(m)` in `SL₂(ℤ)`. -/
abbrev Gamma0RightCosets (m : ℕ+) :=
  Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ)))

noncomputable instance gamma0RightCosetsFintype (m : ℕ+) :
    Fintype (Gamma0RightCosets m) := by
  letI : NeZero (m : ℕ) := ⟨PNat.ne_zero m⟩
  haveI : (CongruenceSubgroup.Gamma0 (m : ℕ)).FiniteIndex := by infer_instance
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (m : ℕ)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact Fintype.ofEquiv (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (m : ℕ))
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (s := CongruenceSubgroup.Gamma0 (m : ℕ))).symm

/-- Cox Lemma 11.11.  The proof is the rank-two HNF classification of the relevant
determinant-`m` primitive matrices. -/
noncomputable def coxMatrixEquivRightCosets (m : ℕ+) :
    CoxMatrix m ≃ Gamma0RightCosets m := by
  sorry

/-- The conjugate `j(m γ τ)` attached to a right coset. -/
noncomputable def rightCosetEval (m : ℕ+) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ := by
  sorry

/-- Translate a `Γ₀(m)`-modular function by a right coset; invariance makes this independent
of the representative. -/
noncomputable def rightCosetTranslate (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ := by
  sorry

/-- Cox's distinguished matrix `σ₀ = diag(m,1)`. -/
noncomputable def sigmaZero (m : ℕ+) : CoxMatrix m := by
  sorry

/-- Cox equation (11.12), expressed through the HNF/right-coset equivalence. -/
theorem rightCosetEval_equiv (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) :
    rightCosetEval m (coxMatrixEquivRightCosets m σ) τ = j (σ.act τ) := by
  sorry

/-- The distinguished Cox matrix corresponds to the identity right coset, so translating by
it leaves a modular function unchanged. -/
theorem rightCosetTranslate_sigmaZero (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) :
    rightCosetTranslate m hf (coxMatrixEquivRightCosets m (sigmaZero m)) τ = f τ := by
  sorry

theorem j_act_sigmaZero (m : ℕ+) :
    (fun τ ↦ j ((sigmaZero m).act τ)) = levelJ m := by
  sorry

/-- Cox's count `|C(m)| = m ∏_{p∣m}(1+1/p)`, written in `ℚ` to keep the displayed
Euler product literal. -/
theorem card_coxMatrix (m : ℕ+) :
    (Fintype.card (CoxMatrix m) : ℚ) =
      (m : ℚ) * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ)) := by
  sorry

/-- The primitive `m`-th root used in equation (11.13). -/
def zeta (m : ℕ+) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

theorem zeta_isPrimitiveRoot (m : ℕ+) : IsPrimitiveRoot (zeta m) (m : ℕ) := by
  sorry

/-- The integral Laurent coefficient of the analytic `j`-function. -/
noncomputable def jIntCoeff (n : ℤ) : ℤ :=
  (jLaurentqExpansion_isIntegral (n := n)).choose

theorem jIntCoeff_spec (n : ℤ) :
    (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ) := by
  sorry

theorem jIntCoeff_neg_one : jIntCoeff (-1) = 1 := by
  sorry

/-- Equation (11.13) as a formal Laurent series in `t=q^(1/m)`. -/
noncomputable def transformedJSeries {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) : LaurentSeries K :=
  ⟨fun k ↦ if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0,
   by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-((σ.a : ℤ) ^ 2), fun k hk ↦ ?_⟩
    simp only [Function.mem_support, ne_eq] at hk
    by_contra h
    apply hk
    rw [if_neg]
    exact fun h' ↦ h h'.2⟩

theorem transformedJSeries_coeff {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) (k : ℤ) :
    (transformedJSeries ζ σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0 := rfl

/-- The exact analytic/formal bridge for (11.13).  The width is `m`, not `1`: its local
parameter is `q^(1/m)`. -/
theorem laurentqExpansion_coxAction (m : ℕ+) (σ : CoxMatrix m) :
    laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j (σ.act τ)) =
      transformedJSeries (zeta m) σ := by
  sorry

/-- Galois reindexing `b ↦ bk (mod d)` from the proof of Theorem 11.18(i). -/
noncomputable def reindex {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    CoxMatrix m → CoxMatrix m := by
  sorry

theorem reindex_bijective {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    Function.Bijective (reindex k hk) := by
  sorry

end Cox
