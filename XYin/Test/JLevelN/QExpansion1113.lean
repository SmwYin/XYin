import XYin.Test.JLevelN.CM

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries Polynomial
open scoped Manifold

/-!
# Cox equation (11.13): the q-expansion of `j(στ)` (skeleton, G2 — technical crux)

Cox eq. (11.13), p. 229:
`j(στ) = ζ_m^{-ab}/(q^{1/m})^{a²} + Σ_{n=0}^∞ c_n ζ_m^{abn}(q^{1/m})^{a²n}`, with `c_n ∈ ℤ`
the integer q-coefficients of `j`.

We model this as a formal `LaurentSeries K` in the variable `t = q^{1/m}` over an arbitrary
field `K` carrying a root `ζ` (the cyclotomic specifics enter only in the Galois descent of
part (i), file `GaloisDescent.lean`).  The integer coefficients `c_n` come from the
sorry-free `jfunctionLaurent.jLaurentqExpansion_isIntegral`.

`jSigma` is given by its explicit coefficient function; only the (clearly true) PWO-support
side condition — the support is `{a²n : n ≥ -1}`, bounded below by `-a²` — is left `sorry`.
-/

noncomputable section

section IntegerJCoefficients

/-- The integer q-expansion coefficient `c_n ∈ ℤ` of the `j`-function at exponent `n`
(Cox Theorem 11.8), extracted from the sorry-free `jLaurentqExpansion_isIntegral`. -/
noncomputable def jIntCoeff (n : ℤ) : ℤ := (jLaurentqExpansion_isIntegral (n := n)).choose

/-- Defining property: `(laurentqExpansion 1 j).coeff n = c_n`. -/
theorem jIntCoeff_spec (n : ℤ) :
    (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ) :=
  (jLaurentqExpansion_isIntegral (n := n)).choose_spec

/-- The residue `c_{-1} = 1` (the simple pole `1/q` of `j`). -/
theorem jIntCoeff_neg_one : jIntCoeff (-1) = 1 := by
  have h := jIntCoeff_spec (-1)
  rw [jLaurentqExpansion_minusone] at h
  exact_mod_cast h.symm

/-- Below the pole there are no terms: `c_n = 0` for `n < -1`. -/
theorem jIntCoeff_lt_neg_one {n : ℤ} (hn : n < -1) : jIntCoeff n = 0 := by
  have h := jIntCoeff_spec n
  rw [jLaurentqExpansion_lt_minusone hn] at h
  exact_mod_cast h.symm

end IntegerJCoefficients

section JSigma

variable {K : Type*} [Field K] {m : ℕ+}

/-- **Cox eq. (11.13)** as a formal Laurent series in `t = q^{1/m}` over `K`: for
`σ = (a b; 0 d) ∈ C(m)` and a root `ζ : K`,
`jSigma ζ σ = Σ_{n ≥ -1} c_n ζ^{abn} t^{a²n}`, i.e. the coefficient of `t^k` is
`c_{k/a²} ζ^{ab·(k/a²)}` when `a² ∣ k` and `k ≥ -a²`, else `0`. -/
noncomputable def jSigma (ζ : K) (σ : CM m) : LaurentSeries K :=
  ⟨fun k => if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
            then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
              ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
            else 0,
   by
     apply Set.IsWF.isPWO
     apply BddBelow.isWF
     refine ⟨-((σ.a : ℤ) ^ 2), fun k hk => ?_⟩
     simp only [Function.mem_support, ne_eq] at hk
     by_contra hc
     apply hk
     rw [if_neg]
     rintro ⟨-, h2⟩
     omega⟩

/-- The (11.13) coefficient formula (definitional). -/
theorem jSigma_coeff (ζ : K) (σ : CM m) (k : ℤ) :
    (jSigma ζ σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0 := rfl

/-- The most-negative term of (11.13): the coefficient of `t^{-a²}` is `ζ^{-ab}`
(the pole term, using `c_{-1} = 1`). Cox (11.19) uses this for part (iv). -/
theorem jSigma_botCoeff (ζ : K) (σ : CM m) :
    (jSigma ζ σ).coeff (-((σ.a : ℤ) ^ 2)) = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ))) := by
  have ha : (σ.a : ℤ) ≠ 0 := by exact_mod_cast σ.ha.ne'
  have ha2 : (σ.a : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hdiv : (-((σ.a : ℤ) ^ 2)) / (σ.a : ℤ) ^ 2 = -1 := by
    rw [show -((σ.a : ℤ) ^ 2) = (σ.a : ℤ) ^ 2 * (-1) by ring]
    exact Int.mul_ediv_cancel_left _ ha2
  rw [jSigma_coeff, if_pos ⟨dvd_neg.mpr (dvd_refl _), le_refl _⟩, hdiv, jIntCoeff_neg_one]
  simp

/-- Below `-a²` the series vanishes (the pole order is `a²`). -/
theorem jSigma_coeff_eq_zero_of_lt {ζ : K} {σ : CM m} {k : ℤ}
    (hk : k < -((σ.a : ℤ) ^ 2)) : (jSigma ζ σ).coeff k = 0 := by
  rw [jSigma_coeff, if_neg]
  rintro ⟨-, h2⟩
  omega

end JSigma

section AnalyticBridge

/-- **Bridge leaf (analytic ↔ formal), Cox eq. (11.13)** and Cox p. 232 ("the coefficients of
the q-expansion are algebraic integers").  The `q`-expansion coefficients of the analytic Cox
root `z ↦ j (στ)` (with `στ = cmAction σ z = (aτ+b)/d`) are algebraic integers: they are the
`ℤ[ζ_m]`-coefficients of the formal series `jSigma` at `ζ_m = e^{2πi/m}` (variable `t = q^{1/m}`).
This is the analytic input feeding the Galois descent of part (i)
(`GaloisDescent.coxPhiFunction_coeff_integer_qExpansion`); the precise `jSigma`-identification
(with the width-`m` cusp expansion) is the content of the proof. -/
theorem cmAction_root_qExpansion_isIntegral (m : ℕ+) (σ : CM m) (k : ℤ) :
    IsIntegral ℤ ((laurentqExpansion 1 (fun z => j (σ.cmAction z))).coeff k) := by
  sorry -- T011: analytic↔formal bridge; needs laurentqExpansion width/algebra API (absent in LaurentQExpansion). Substantial.

end AnalyticBridge
