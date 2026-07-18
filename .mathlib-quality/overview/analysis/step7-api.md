# Step 7 — API-Design Review (missing lemmas, simp API, instances, completeness)

Scope: all inventories in `.mathlib-quality/overview/inventory/` plus source verification under
`XYin/` (excluding `PhD/Modularforms/`). Line numbers refer to current working-tree state.

---

## 1. Missing Lemmas (repeated proof patterns)

### **Need: `UpperHalfPlane.analyticAt_cuspFunction_of_eventuallyEq`** (with companion `cuspFunction_apply_zero_eq`)
- **Pattern** (6 occurrences): the 10-line "glue" calc block
  `F 0 = limUnder (𝓝[≠] 0) F = limUnder (𝓝[≠] 0) G = G 0` via
  `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` + `Filter.map_congr` + `limUnder_eq`,
  followed by `AnalyticAt.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE …)`.
  - `LaurentQExpansion/LaurentQExpansion.lean:348-359` (top branch of `analyticAt_cuspFunction_poleRemoved`)
  - `LaurentQExpansion/LaurentQExpansion.lean:380-391` (k < 0 branch)
  - `LaurentQExpansion/LaurentQExpansion.lean:407-418` (k ≥ 0 branch)
  - `LaurentQExpansion/LaurentQExpansion.lean:444-455` (h ≤ 0 branch)
  - `LaurentQExpansion/LaurentQExpansion.lean:496-508` (`analyticAt_cuspFunction_of_not_pos`)
  - `LaurentQExpansion/Algebra.lean:42-53` (`cuspFunction_qpow_mul_eventuallyEq`)
- **Proposed statement**:
  ```lean
  /-- If the cusp function agrees with `G` on a punctured neighbourhood of `0` and `G` is
  continuous at `0`, then the (limUnder-defined) cusp value at `0` is `G 0`. -/
  lemma cuspFunction_apply_zero_eq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
      (hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] G) (hG : ContinuousAt G 0) :
      cuspFunction h f 0 = G 0

  lemma analyticAt_cuspFunction_of_eventuallyEq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
      (hG : AnalyticAt ℂ G 0) (hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] G) :
      AnalyticAt ℂ (cuspFunction h f) 0
  ```
  (The constant-`G` cases are `G = fun _ ↦ c` with `continuousAt_const`.)
- **Estimated savings**: ~12 lines × 6 sites ≈ 70 lines; `analyticAt_cuspFunction_poleRemoved`
  drops from 132 to ~60 lines. Also removes the exact duplicate
  `cuspFunction_to_analyticAt_analyticAt` naturally.

### **Need: `Periodic.cuspFunction_eventuallyEq_comp_invQParam`** (single "pointwise-op transfer" source)
- **Pattern** (7+ occurrences): "off `0` the cusp function is just evaluation at
  `ofComplex (invQParam h q)`, so cuspFunction commutes with any pointwise operation on a
  punctured neighbourhood" — re-proved per operation:
  - `LaurentQExpansion/LaurentQExpansion.lean:43-52, 54-63, 65-71`
    (`cuspFunction_add/mul/const_eventuallyEq`)
  - `Cox/ModularFunction.lean` — `cuspFunction_sub_const_mul_pow_eventuallyEq` (~line 500),
    `cuspFunction_mul_eventuallyEq` (~line 875), `cuspFunction_polynomial_eval_eventuallyEq`
    (inventory notes: "a general 'cuspFunction commutes with pointwise operations off 0' lemma
    would subsume all three")
  - `LaurentQExpansion/Algebra.lean:245-254` (`analyticAt_cuspFunction_const` re-derivation);
    plus the inline `cuspFunction h 1 = 1` blocks in `qExpansion_qParam_pow` and
    `qExpansion_qpow_mul` (Algebra.lean:63-105).
- **Proposed statement**:
  ```lean
  lemma cuspFunction_eventuallyEq_eval (h : ℝ) (f : ℍ → ℂ) :
      cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)]
        fun q ↦ f (UpperHalfPlane.ofComplex (Periodic.invQParam h q))
  ```
  Every op-specific `_eventuallyEq` lemma then becomes a 2-line `filter_upwards` over three
  instances of this lemma. Optionally keep one n-ary corollary:
  ```lean
  lemma cuspFunction_map₂_eventuallyEq (op : ℂ → ℂ → ℂ) :
      cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0]
        fun q ↦ op (cuspFunction h f q) (cuspFunction h g q)
  ```
- **Estimated savings**: ~40 lines and, more importantly, makes future ops (sub, div, smul) free.

### **Need: `analyticOrderAt_const_mul_pow`**
- **Pattern** (3 occurrences): the block proving `analyticOrderAt (fun q ↦ c * q ^ r) 0 = r`
  (+ its `¬EventuallyConst` corollary) via `analyticOrderAt_mul`, `analyticOrderAt_pow`,
  `analyticOrderAt_id`, `eventuallyConst_iff_analyticOrderAt_sub_eq_top`:
  - `LaurentQExpansion/LaurentQExpansion.lean:227-239` and again `:240-244`
    (inventory: "duplicated verbatim twice inside `meromorphicOrderAt_cuspFunction_nat_mul`")
  - `Cox/CoxMatrices/LaurentExpansion.lean:168-195` (first 28 lines of `poleOrder_coxAction_aux`)
- **Proposed statement**:
  ```lean
  lemma analyticOrderAt_const_mul_pow {c : ℂ} (hc : c ≠ 0) (r : ℕ) :
      analyticOrderAt (fun q : ℂ ↦ c * q ^ r) 0 = r

  lemma not_eventuallyConst_const_mul_pow {c : ℂ} (hc : c ≠ 0) {r : ℕ} (hr : r ≠ 0) :
      ¬ Filter.EventuallyConst (fun q : ℂ ↦ c * q ^ r) (𝓝 (0 : ℂ))
  ```
- **Estimated savings**: ~35 lines across the two files; `poleOrder_coxAction_aux` 54 → ~25.

### **Need: `UpperHalfPlane.poleOrder_eq_of_meromorphicOrderAt_eq`**
- **Pattern** (4 occurrences): the tail block
  "`unfold poleOrder; rw [hord]; prove (-(r:ℤ) : WithTop ℤ) < 0; rw [if_pos]; untopD/natAbs`":
  - `jFunction/jfunction.lean:750-756` (`j_poleOrder`)
  - `Cox/CoxMatrices/LaurentExpansion.lean:216-223` (tail of `poleOrder_coxAction_aux`)
  - `LaurentQExpansion/LaurentQExpansion.lean:251-291` (`poleOrder_nat_mul`, the `WithTop ℤ`
    cast bookkeeping is exactly this pattern under a case split)
  - `LaurentQExpansion/LaurentQExpansion.lean:666-687` (theorem `order`)
- **Proposed statement**:
  ```lean
  lemma poleOrder_eq_of_meromorphicOrderAt_eq {h : ℝ} {f : ℍ → ℂ} {r : ℕ}
      (hord : meromorphicOrderAt (cuspFunction h f) 0 = (-(r : ℤ) : WithTop ℤ)) :
      poleOrder h f = r
  ```
  (Valid for `r = 0` too — both branches of the `if` give `0` — so no positivity side condition.)
  Together with the existing converse `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`
  this makes `poleOrder` fully order-characterised and the `if-then-else` never unfolds again.
- **Estimated savings**: ~8 lines × 4 sites, plus every future pole-order computation.

### **Need: `laurentqExpansion_pow` and `laurentqExpansion_polynomial_eval₂`** (in `LaurentQExpansion/Algebra.lean`)
- **Pattern** (2 near-verbatim ~40-line inductions + 2 aux pow lemmas):
  - `Cox/ModularPolynomial/IntegralDescent.lean:24-68`
    (`laurentqExpansion_j_pow_aux` + `laurentqExpansion_polynomialIn_j_aux`, width 1)
  - `Cox/DiagonalLaurent.lean:164-216`
    (`laurentqExpansion_j_pow_widthM` + `laurentqExpansion_polynomialIn_j_widthM`, width m)
  Both do `Polynomial.induction_on'` with `laurentqExpansion_add`/`_mul` and a
  `finset_prod`-derived pow step, differing only in the width parameter and the meromorphy witness.
- **Proposed statements**:
  ```lean
  theorem laurentqExpansion_pow {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
      (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
      laurentqExpansion h (fun τ ↦ f τ ^ n) = laurentqExpansion h f ^ n

  theorem laurentqExpansion_polynomial_eval₂ {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
      (hf : MeromorphicAt (cuspFunction h f) 0) (P : Polynomial ℂ) :
      laurentqExpansion h (fun τ ↦ P.eval (f τ)) =
        P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)
  ```
  (`laurentqExpansion_pow` follows from `laurentqExpansion_finset_prod` over `Finset.range n`
  with meromorphy of powers from `meromorphicAt_cuspFunction_mul`; the polynomial lemma then
  needs no per-`f` meromorphy family.) A companion
  `meromorphicAt_cuspFunction_polynomial_eval` subsumes
  `polynomialIn_cuspMeromorphicAt_aux` (IntegralDescent.lean:30) and
  `polynomialIn_widthM_cuspMeromorphicAt` (DiagonalLaurent.lean:170) and the private
  `meromorphicAt_polynomial_eval` in ModularFunction.lean (~line 900).
- **Estimated savings**: ~90 lines deleted across IntegralDescent + DiagonalLaurent; the two
  38-line duplicates become 1-line specialisations.

### **Need: `symmetricCubicExpansion_coeff` (index-generic)**
- **Pattern** (4 identical 18-line proofs): `Cox/SymmetricCubicLaurent.lean:44-118`,
  `symmetricCubicExpansion_coeff_zero/_one/_two/_three` are character-identical except for the
  index literal (the proof body never mentions the index outside `hinner`).
- **Proposed statement**:
  ```lean
  private theorem symmetricCubicExpansion_coeff {K : Type*} [CommRing K]
      (P : BivariatePolynomial K) {i : ℕ} (hi : i ≤ 3)
      (hinner : (P.coeff i).natDegree ≤ 3)
      (hsymm : Polynomial.Bivariate.swap P = P) :
      (symmetricCubicExpansion P).coeff i = P.coeff i := by
    interval_cases i <;> · apply Polynomial.ext; intro j; by_cases hj : j ≤ 3 <;> …
  ```
  (One `interval_cases i <;>` over the shared body; `eq_symmetricCubicExpansion` at
  lines 120-141 then calls it uniformly with `(hinner i)`.)
- **Estimated savings**: ~55 lines; removes 3 declarations.

### **Need: `CoxMatrix.ofColumnHNF` smart constructor**
- **Pattern** (2 occurrences, flagged in inventory): the ~28-line "repackage an
  `IsColumnHermiteNormalForm` matrix with `det = m` and content 1 as a `CoxMatrix` via `natAbs`"
  block is duplicated:
  - `Cox/CoxMatrices/Basic.lean:434-461` (inside `exists_coxMatrix_reduction`, 59-line proof)
  - `Cox/CoxMatrices/Basic.lean:904-938` (`exists_coxMatrix_of_isColumnHermiteNormalForm_aux`)
- **Proposed statement**:
  ```lean
  def CoxMatrix.ofColumnHNF {m : ℕ+} (H : Matrix (Fin 2) (Fin 2) ℤ)
      (hHNF : H.IsColumnHermiteNormalForm) (hdet : H.det = (m : ℕ))
      (hcont : Matrix.rankTwoContent H = 1) : CoxMatrix m

  @[simp] theorem CoxMatrix.inclusionMatrix_ofColumnHNF … :
      (CoxMatrix.ofColumnHNF H hHNF hdet hcont).inclusionMatrix = H
  ```
- **Estimated savings**: ~30 lines; `exists_coxMatrix_reduction` 59 → ~30 and
  `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` 35 → ~8.

### **Need: `UpperHalfPlane.natScale` — one home for `τ ↦ N·τ` on ℍ**
- **Pattern** (2 independent definitions + 1 heavily-used aux lemma): the fact
  `0 < im z → 0 < im (N·z)` and the packaged map ℍ → ℍ are built independently:
  - `jFunction/jLevelN.lean:32-36` `natCast_mul_im_pos_aux` — used by **8** declarations in that
    file, always through anonymous-constructor terms `⟨(N:ℂ) * z, natCast_mul_im_pos_aux …⟩`
  - `Cox/ModularFunction.lean:180-189` `natScaleUpperHalfPlane` (private) + `coe_natScaleUpperHalfPlane`
  - (related: `Cox/CoxMatrices/Basic.lean:80-92` `CoxMatrix.act` proves the general
    `(aτ+b)/d` positivity, of which this is the `b=0, d=1` case)
- **Proposed statement** (central, e.g. in a small `XYin/PhD/UpperHalfPlaneMaps.lean` or at the
  top of jLevelN):
  ```lean
  def UpperHalfPlane.natScale (N : ℕ) [NeZero N] (τ : ℍ) : ℍ := ⟨N * τ, by …⟩
  @[simp] lemma UpperHalfPlane.coe_natScale : (natScale N τ : ℂ) = N * τ
  lemma UpperHalfPlane.natScale_ofComplex {w : ℂ} (hw : 0 < w.im) :
      natScale N (ofComplex w) = ofComplex (N * w)   -- today natCast_mul_ofComplex_coe_aux
  ```
  Then `jN N = j ∘ natScale N`, `qjN N = qj ∘ natScale N`, and ModularFunction.lean deletes its
  private duplicate.
- **Estimated savings**: modest in lines (~20) but removes 8 anonymous-constructor terms whose
  proofs re-elaborate at every use, and unifies two files' vocabulary.

### **Need: one canonical `jIntCoeff` (integer coefficients of j) with cast API**
- **Pattern** (3 independent noncanonical extractions of the same integers, each with its own
  spec/cast bridge):
  - `jFunction/jfunction.lean:393` `qjCoeffs : ℕ → ℤ` (via `toIntegralPowerSeries`, i.e.
    `Classical.choose`), bridge `qj_coeff_cast_aux` (line 395), used by 8 decls;
    re-bridged again in `jFunction/qexp_coeffs.lean:41-48`
    (`qjCoeffs_eq_qjQExpansion_coeff_aux`).
  - `Cox/CoxMatrices/LaurentExpansion.lean:31` `jIntCoeff : ℤ → ℤ` (via `Classical.choose` on
    `j_laurentQExpansion_isIntegral`), bridge `jIntCoeff_spec` (line 34).
  - `qExpansion_tactic/Qj.lean:112` `qjCoeffInt : ℕ → ℤ` (computable table), bridged to the
    analytic side by `link.lean:456` `qjCoeffInt_eq` and to `jIntCoeff` by
    `Cox/LevelThree.lean:122` `jIntCoeff_eq_qjCoeffInt_three`.
- **Proposed design**: make `jIntCoeff (n : ℤ) : ℤ` the single source of truth (keep the
  `Classical.choose` definition or, better, define it from `qjCoeffs (n+1).toNat` so there is only
  one choice), and provide the lemma set
  ```lean
  @[simp] lemma jIntCoeff_cast (n : ℤ) : ((jIntCoeff n : ℤ) : ℂ) = (laurentqExpansion 1 j).coeff n
  @[simp] lemma qjCoeffs_eq (n : ℕ) : qjCoeffs n = jIntCoeff (n - 1)
  @[simp] lemma jIntCoeff_neg_one : jIntCoeff (-1) = 1
  lemma jIntCoeff_eq_qjCoeffInt (n : ℕ) : jIntCoeff n = qjCoeffInt (n + 1)  -- computable eval
  ```
- **Estimated savings**: eliminates 2 `Classical.choose` definitions, ~6 bridge lemmas scattered
  over 4 files (jfunction, qexp_coeffs, LaurentExpansion, LevelThree), and the per-file cast
  dances they cause.

### **Need: sphere-membership helpers for contour integrals**
- **Pattern** (duplicated inside the 151-line `laurentqExpansion_coeff_eq_circleIntegral`,
  `LaurentQExpansion/LaurentQExpansion.lean:819-971`): the sub-proofs "`z ∈ sphere 0 R → z ≠ 0`"
  and "`z ∈ sphere 0 R → ‖z‖ < 1`" (for `R < 1`) each appear twice, and the two `EqOn`-on-sphere
  calc blocks both do the same `zpow_add₀`/`zpow_sub₀` exponent bookkeeping.
- **Proposed statements**:
  ```lean
  lemma ne_zero_of_mem_sphere' {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ Metric.sphere (0:ℂ) R) : z ≠ 0
  lemma norm_lt_one_of_mem_sphere {R : ℝ} (hR : R < 1) {z : ℂ} (hz : z ∈ sphere (0:ℂ) R) : ‖z‖ < 1
  lemma zpow_mul_zpow_eq {z : ℂ} (hz : z ≠ 0) (a b : ℤ) : z ^ a * z ^ b = z ^ (a + b)  -- alias of zpow_add₀
  ```
  plus stating the two `EqOn` blocks once as a lemma
  `cuspFunction_div_zpow_eqOn_sphere` used by both branches.
- **Estimated savings**: 151 → ~90 lines.

### **Need: `qExpansion_coeff_eq_intCast_of` cast-dance helper**
- **Pattern** (8 occurrences): `jFunction/qexp_coeffs.lean:54-116` — every numeric coefficient
  lemma is the same 4-line block
  `rw [X_qxp_coeff_link]; exact_mod_cast (show F.coeff n = (c : ℤ) by rw [F_coeff_eq]; rfl)`
  for `X ∈ {Delta, qj}`, `n ∈ {1..5}`.
- **Proposed statement**:
  ```lean
  lemma coeff_eq_intCast_of_link {f : ℍ → ℂ} {F : PowerSeries ℤ}
      (link : ∀ k, (qExpansion 1 f).coeff k = (F.coeff k : ℂ))
      {n : ℕ} {c : ℤ} (h : F.coeff n = c) : (qExpansion 1 f).coeff n = (c : ℂ)
  ```
  Each site becomes `coeff_eq_intCast_of_link Delta_qxp_coeff_link (by rw [...]; rfl)`.
- **Estimated savings**: ~20 lines; pattern also reusable by the Tactic2 test files.

### **Need: generalised jet machinery (LevelThree)**
- **Pattern**: `Cox/LevelThree.lean` contains ~35 private `decide +kernel` lemmas
  (`explicitCandidateClearedJet{Term,Row,}Three_*`, inventory lines 446-830) that split one large
  kernel computation into per-row/per-term pieces purely to keep each `decide` within kernel
  budget, plus the jet infrastructure `jetMul/jetPow/jetShift/jetExpand` hard-coded to window
  `n < 37`. The file summary itself flags: "the jet infrastructure … duplicates a pattern likely
  needed for other levels; candidates for generalisation and extraction."
- **Proposed design**: extract a level-generic module `Cox/JetCertificate.lean`:
  ```lean
  def jet (N : ℕ) := Fin N → ℤ           -- truncated integer Laurent jet
  def jetMul / jetPow / jetShift / jetExpand  -- window-parametric, with the three soundness
  theorem powerSeries_coeff_mul_eq_jetMul (N) …  -- lemmas proved once for any window
  ```
  and drive the per-coefficient checks with a `Finset`-indexed statement
  `∀ k ∈ observedSet, clearedJet k = 0` proved by `decide +kernel` on a single folded boolean
  (or `fin_cases k <;> decide +kernel` in one lemma), instead of ~35 named lemmas.
- **Estimated savings**: ~350 lines in LevelThree now, and the entire module is reusable for
  Φ₂/Φ₅/… later; per-lemma naming discipline (`_eighteen_three_two` …) disappears.

---

## 2. Missing simp lemmas

Project-wide there are only **53** `@[simp]` attributes over ~16 000 lines; the central analytic
files have almost none (`LaurentQExpansion.lean`: 0, `CoxMatrices/LaurentExpansion.lean`: 0,
`ModularPolynomial/Construction.lean`: 1). Kronecker.lean (11) shows the intended style.

### **Need: simp set for `laurentqExpansion` coefficients**
- `laurentqExpansion.coeff_neg_poleOrder_add`, `laurentqExpansion.coeff_zero`,
  `laurentqExpansion.coeff_neg_poleOrder` (LaurentQExpansion.lean:544-591) are unconditional
  equations and prime `@[simp]` candidates; `coeff_of_qExpansion` (the if-then-else closed form,
  line 575) is the canonical unfolding lemma the Tactic2 `qexp_simp` attribute set should carry.
  Currently the file's *only* users of these must `rw` by hand.
- `transformedJSeries_coeff` (CoxMatrices/LaurentExpansion.lean:66, proof `rfl`) — mark `@[simp]`.

### **Need: defining-equation simp lemmas for the four core defs**
`poleOrder`, `poleRemoved`, `to_qExpansion`, `laurentqExpansion`
(LaurentQExpansion.lean:209-301) have **no docstrings and no API-normal-form lemmas**; proofs
throughout the project `unfold UpperHalfPlane.poleOrder` / `simp [UpperHalfPlane.poleRemoved]`
(e.g. jfunction.lean:750, LaurentExpansion.lean:216, Algebra.lean passim). Provide:
```lean
@[simp] lemma poleRemoved_apply : poleRemoved h f τ = 𝕢 h τ ^ poleOrder h f * f τ
lemma poleOrder_eq_zero_iff (hmero) : poleOrder h f = 0 ↔ AnalyticAt ℂ (cuspFunction h f) 0
  -- (today `analyticAt_iff`, whose bare root-namespace name should change anyway)
@[simp] lemma poleRemoved_of_poleOrder_eq_zero (h0 : poleOrder h f = 0) : poleRemoved h f = f
```
The last one is re-derived inline at least 3× (`analyticAt_iff` backward branch, LaurentQExpansion.lean:466-468;
`eq_qExpansion_iff` backward branch, :755 region; `cuspFunction_poleRemoved_eq` h ≤ 0 branch).

### **Need: `@[simp]` on the `BivariatePolynomial` normalisation lemmas**
`Construction.lean` defines `specializeY_eval`, `eval_swap`, `coeff_coeff_swap`, `map_swap`,
`diagonal_eval`, `diagonal_map`, `diagonal_eval₂`, `diagonal_swap` (inventory lines 105-203) —
none is `@[simp]` although downstream files (`SymmetricCubicLaurent.lean:26`, `LevelThree.lean:777,805`,
`SingularModuli.lean:225`, `Arithmetic.lean:117`) always use them as left-to-right rewrites.
Marking `coeff_coeff_swap`, `specializeY_eval`, `diagonal_eval`, `map_swap` as `@[simp]` matches usage.

### **Need: `CoxMatrix` coe/act simp set completion**
`CoxMatrix.coe_act` is `@[simp]` but there is no `@[simp]` for
`inclusionMatrix`/`mobiusMatrix` entries (`inclusionMatrix 0 0 = σ.d` etc.), forcing
`simp only [CoxMatrix.inclusionMatrix, Matrix.of_apply, Matrix.cons_val_zero, …]` boilerplate
(Basic.lean:354 and several HNF proofs). Four entry lemmas per matrix would replace those lists.

### Status notes (verified)
- `CyclicSublattice` **has** an `@[ext]` lemma (CyclicSublattice.lean:35); it is unused in-file
  but consumed by Classification.lean — fine, no action.
- `laurentqExpansion_zero/_one/_const` are already `@[simp]` (Algebra.lean) — good; `_const`
  subsumes the other two as noted in the inventory; keep all three (simp-normal-form idiom).

---

## 3. Missing Instances / Coercions

### **Need: `@[ext] theorem CoxMatrix.ext`**
- `CoxMatrix` (Basic.lean:24) is a 7-field structure whose equality is repeatedly established by
  hand-rolled field extraction:
  - `toFin_injective` (Basic.lean:105-112): `congrArg (fun x ↦ x.1.val)` ×3 then `cases; simp_all`
  - `CoxMatrix.inclusionMatrix_injective` (Basic.lean:348-…): same shape
  - `reindex_bijective` (CoxMatrices/LaurentExpansion.lean:428-458) ends via `toFin_injective`
  - `transformed_injective` (UpperHalfPlaneFunctionField.lean, inventory line 316) ends via
    `toFin_injective`
- **Proposed**:
  ```lean
  @[ext] theorem CoxMatrix.ext {σ τ : CoxMatrix m}
      (ha : σ.a = τ.a) (hb : σ.b = τ.b) (hd : σ.d = τ.d) : σ = τ
  ```
  (Proof: `cases σ; cases τ; simp_all` — proof fields are propositions.) All four proofs above
  shrink to `ext <;> …`.
- **Estimated savings**: ~15 lines + idiomatic `ext` availability everywhere `CoxMatrix` equality arises.

### **Need: evaluation API for `HolomorphicFunction` instead of `.1 τ`**
- `HolomorphicFunction := holomorphicFunctions` (UpperHalfPlaneFunctionField.lean:39) is a
  subalgebra; there is already a bundled `evaluation (tau : ℍ) : HolomorphicFunction →+* ℂ`
  (line 69), yet proofs use raw subtype application 11× across
  UpperHalfPlaneFunctionField.lean / ModularFunctionField.lean, including the fragile idiom
  `congrArg (fun f : HolomorphicFunction ↦ f.1 τ)` (3 occurrences: UHPFF:91, :309, MFF:120).
- **Proposed**: add
  ```lean
  instance : FunLike HolomorphicFunction ℍ ℂ := ⟨fun f ↦ f.1, Subtype.coe_injective⟩
  @[simp] lemma evaluation_apply (τ : ℍ) (f : HolomorphicFunction) : evaluation τ f = f τ
  @[ext] lemma HolomorphicFunction.ext (h : ∀ τ, f τ = g τ) : f = g
  ```
  and route the `congrArg` sites through `map_*` lemmas of `evaluation`.
- **Estimated savings**: small in lines, large in readability; unblocks `simp`/`map_pow`-style
  reasoning about evaluations (used ad hoc in `represents_unique`, 26 lines).

### **`IsGamma0ModularFunction`: keep the predicate, complete the closure API**
- Converting to a FunLike structure is **not** recommended: 14 users consume it as a plain
  `Prop` on `ℍ → ℂ` and mix bare functions (`j`, `levelJ N`, pointwise lambdas) freely; bundling
  would force wrapping/unwrapping at every lambda. What is actually missing is the closure
  lemma set: today only `IsGamma0ModularFunction.mul` (ModularFunction.lean:888) and
  `.polynomialIn` (:927) are public, while `sub_const_mul_pow` (:525) is a private one-off shape.
- **Proposed** (each ≤ 8 lines once the `cuspFunction_eventuallyEq_eval` transfer lemma of §1
  exists): `IsGamma0ModularFunction.add`, `.sub`, `.neg`, `.const` (incl. `zero`, `one`),
  `.pow`, `.smul`. Then `isGamma0ModularFunction_sub_const_mul_pow` becomes
  `hf.sub ((hg.pow m).const_mul a)` and can be deleted.
- **Estimated savings**: replaces the bespoke 30-line private lemma; future Cox-chapter arguments
  (Φ-coefficient manipulations in Construction/IntegralDescent) get an algebra of modular
  functions for free.

### **Need: naming/dedup hygiene in root namespace** (blocking safe instance/simp work)
- `analyticAt_iff` (LaurentQExpansion.lean:457) and `order` (:666) are dangerously generic root
  names; `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (:662) is an *exact duplicate* of
  `…_of_ne_zero` (:593); `cuspFunction_to_analyticAt_analyticAt` (:793) duplicates
  `analyticAt_cuspFunction_poleRemoved`. Rename/delete before adding simp attributes, or the simp
  set will carry duplicates.

---

## 4. API Completeness Gaps (per major definition)

### `laurentqExpansion` (LaurentQExpansion.lean + Algebra.lean)
| op | status |
|---|---|
| `zero/one/const` | ✔ `@[simp]` |
| `add`, `mul` | ✔ |
| `neg` | ✔ (unused so far) |
| `finset_sum`, `finset_prod` | ✔ (unused so far) |
| `sub` | ✘ missing (trivial from add+neg; needed the moment Φ-difference arguments (LevelThree `modularPolynomialThreeDifference`) move to the analytic side) |
| `pow` | ✘ missing — currently re-derived twice as `laurentqExpansion_j_pow_aux` / `_widthM` (see §1) |
| `smul` / `C_mul` | ✘ missing — the `HahnSeries.C a * …` shape is inlined in both polynomialIn inductions |
| `polynomial_eval₂` | ✘ missing (see §1) |
| `inv` / `div` | ✘ — genuinely absent; not yet needed (function-field arguments run through `FunctionField` instead), defer |
| `congr` (`f =ᶠ g` at cusp ⇒ equal expansions) | ✘ — would shortcut several `congr 1; funext τ; simp` blocks |
| period change | ✔ `nat_mul_coeff`, `nat_mul_coeff_of_not_dvd`, `to_qExpansion_nat_mul` |

### `poleOrder`
Has: `nat_mul` scaling, `analyticAt_iff`, order characterisations (with a duplicate), closed form
`order`. Missing: the `poleOrder_eq_of_meromorphicOrderAt_eq` reader (§1), a
`poleOrder_congr` for eventually-equal functions, and `poleOrder_mul_le`/`poleOrder_add_le`
bounds (the sub-`poleOrder` bookkeeping in `exists_const_poleOrder_sub_mul_pow_lt`,
ModularFunction.lean, 49 lines, is exactly an ad-hoc `poleOrder_sub_lt` argument).

### `qj` / `jN` / `levelJ`
- `qj` is complete (periodicity, differentiability, boundedness, analyticity, integrality,
  coefficient values 0-4).
- `jN`/`levelJ`: `levelJ N = jN N` is definitionally re-wrapped (`ModularFunction.lean:29`);
  missing the trivial normalisations `jN 1 = j` / `levelJ 1 = j` (KroneckerFrobenius and
  Arithmetic both special-case level 1 by hand) and `levelJ_apply : levelJ N τ = j (natScale N τ)`
  as `@[simp]`.

### `modularPolynomialC` (Construction.lean)
Has `monic`, `natDegree`, `specializeY`, `rightCosetProduct`, `eval_levelJ_j`, plus IntegralDescent's
`coeff_polynomialIn` and Arithmetic's symmetry/irreducibility consumers. Gap: everything is stated
over `ℂ`; the ℤ-descent (`IntegralDescent`) reconstructs coefficient-integrality through the
private `integerCoeffLaurentSeries : Subring (LaurentSeries ℂ)` (IntegralDescent.lean:123).
That subring duplicates the `HasCoeffsIn`-style layer that `IntegralPowerSeries.lean` already
provides for `PowerSeries` — see next item.

### The change-of-ring layer (`PowerSeries ℤ` / `PowerSeries ℂ` / `LaurentSeries R`)
Current state — four parallel mechanisms:
1. `powerSeriesMapAlgHom R A` + `coeToComplexPowerSeries.ringHom` + `HasCoeffsIn`/lift API
   (IntegralPowerSeries.lean) — power series only;
2. `laurentSeriesMapRingHom` (LaurentPolynomialEvaluation.lean:22) + per-object naturality lemmas
   (`jIntegralLaurentSeries_map_complex`, `jIntegralLaurentSeriesWidth_map_complex/_map_zmod`,
   `specializeJIntegral_map_zmod/_map_complex`, `bivariateSpecializeLaurent_map_apply` — Kronecker.lean,
   22 use sites) — Laurent series;
3. `integerCoeffLaurentSeries : Subring (LaurentSeries ℂ)` (IntegralDescent.lean, private) —
   a second, subring-flavoured formalisation of "integral Laurent series";
4. `jIntCoeff`/`qjCoeffs`/`qjCoeffInt` element-level casts (§1).
**Gap**: no `LaurentSeries` analogue of the `HasCoeffsIn`/`toIntegral…`/round-trip triple, so
IntegralDescent rebuilt it as a subring and Kronecker works purely with explicit `ℤ`-models.
**Proposed**: a small `LaurentIntegralSeries.lean` providing
```lean
def laurentHasCoeffsIn (R A) … (x : LaurentSeries A) : Prop := x ∈ (laurentSeriesMapRingHom (algebraMap R A)).range
lemma laurentHasCoeffsIn_iff_coeff …
def toIntegralLaurentSeries … ; lemma map_toIntegralLaurentSeries …
lemma laurentSeriesMapRingHom_ofPowerSeries :   -- the missing square
    laurentSeriesMapRingHom φ (ofPowerSeries ℤ _ F) = ofPowerSeries ℤ _ (F.map φ)
```
The last commuting square is the one every Kronecker/LevelThree `_map_complex` proof re-proves
coefficientwise. This would also let `integerCoeffLaurentSeries` be deleted.

### `to_qExpansion`
Missing docstring, nonstandard snake_case name for a def (inventory note), and no direct
coefficient lemma `to_qExpansion_coeff : (to_qExpansion h f).coeff n = (n !)⁻¹ • iteratedDeriv …`
— consumers always detour through `laurentqExpansion.coeff_*`. Low priority.

---

## 5. Long proofs and the lemma that would collapse each

| Proof (file:line, length) | Collapsing lemma |
|---|---|
| `analyticAt_cuspFunction_poleRemoved` (LaurentQExpansion.lean:322-455, 132) | `analyticAt_cuspFunction_of_eventuallyEq` + `cuspFunction_apply_zero_eq` (§1) — each of the 4 branches becomes ~8 lines; additionally the h ≤ 0 branch should just call the existing `analyticAt_cuspFunction_of_not_pos` (currently duplicated verbatim below it). 132 → ~55. |
| `laurentqExpansion_coeff_eq_circleIntegral` (LaurentQExpansion.lean:819-971, 151) | sphere-membership + `EqOn` helpers (§1); the two integrand-identification calc blocks become one shared `cuspFunction_div_zpow_eqOn_sphere`. 151 → ~90. |
| `columnHNF_eq_of_mul` (CoxMatrices/Basic.lean:285-345, 61) | genuinely mathematical (2×2 HNF uniqueness); the collapsing lemma is a *mathlib-shaped* `Matrix.IsColumnHermiteNormalForm.eq_of_isUnit_det_mul` — but internally, extracting `diag_eq_of_mutual_dvd : a ∣ b → b ∣ a → 0 < a → 0 < b → a = b` (used twice) and reusing `reduced_eq_of_eq_add_mul_aux` already cuts ~15 lines. Best candidate in the repo for upstreaming rather than golfing. |
| `exists_coxMatrix_reduction` (CoxMatrices/Basic.lean:403-461, 59) | `CoxMatrix.ofColumnHNF` (§1). 59 → ~30, and deletes the 35-line sibling `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` body. |
| `poleOrder_coxAction_aux` (CoxMatrices/LaurentExpansion.lean:168-223, 54) | `analyticOrderAt_const_mul_pow` + `poleOrder_eq_of_meromorphicOrderAt_eq` (§1) + a general `meromorphicOrderAt_cuspFunction_comp_const_mul_pow` corollary. 54 → ~15. |
| `laurentqExpansion_coxAction_coeff_aux` (CoxMatrices/LaurentExpansion.lean:297-388, 90) | `PowerSeries.coeff_smul_rescale_expand : ((c⁻¹ • (rescale c F).expand r hr)).coeff k = …` — one lemma packaging the smul/rescale/expand coefficient formula that cases (ii) and (iii) both unfold by hand; with it plus `jIntCoeff_cast` (§1) the three-way case split shrinks to ~35 lines. |
| `to_qExpansion_coxAction_aux` (CoxMatrices/LaurentExpansion.lean:235-280, 44) and `to_qExpansion_nat_mul` (Algebra.lean:416-463, 46) | both are instances of a missing substitution principle `qExpansion_comp_analytic : F =ᶠ[𝓝 0] G ∘ φ → qExpansion-of-F determined by qExpansion-of-G ∘ φ`; concretely, promote the private `analyticTaylor_comp_pow` (Algebra.lean:369-413, 44 — itself a mathlib candidate about `PowerSeries.expand`) to handle `φ q = c * q^r` (rescale ∘ expand), and both proofs become applications. |
| `laurentqExpansion_mul` (Algebra.lean:202-243, 38) | fine as the workhorse; only note the `hfun` factorisation block shared verbatim with `analyticAt_cuspFunction_qpow_of_poleOrder_le` (Algebra.lean:146-164) — extract `poleRemoved_qpow_factor : (𝔢 h τ)^N * f τ = (𝔢 h τ)^(N-M) * poleRemoved h f τ` once. |
| `exists_const_poleOrder_sub_mul_pow_lt` (ModularFunction.lean, 49) + `levelOne_polynomialInJ_of_holomorphic` (44) | a `poleOrder_sub_lt_of_trailingCoeff_eq` lemma (the private `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq`, 35 lines, is already 90 % of it — publicise and phrase in `poleOrder` terms so the strong-induction driver reads mathematically). |
| `cox_b_eq` (UpperHalfPlaneFunctionField.lean:226-268, 41) | `IsPrimitiveRoot.eq_of_zpow_eq_of_lt : ζ^x = ζ^y → bounds → x = y` — a root-of-unity injectivity-on-a-window lemma; also usable by `reindex_bijective`'s `Nat.ModEq` argument. |
| `aeval_base_eq_zero_of_forall_eval_eq_zero` (Arithmetic.lean, ~44) | a polynomial-vanishing-on-infinite-set lemma is already in mathlib (`Polynomial.eq_zero_of_infinite_isRoot`); the length is the ℂ[X][Y]-to-function plumbing — `BivariatePolynomial.evalEval`-vanishing wrapper would collapse it. |
| `symmetricCubicExpansion` quadruplets (SymmetricCubicLaurent.lean:44-118, 4×18) | index-generic `symmetricCubicExpansion_coeff` (§1). |
| `analyticTaylor_comp_pow`, `meromorphicAt_of_comp_pow`, `eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux` (Algebra.lean/LaurentQExpansion.lean, 44+24+29) | no project-level fix — these are general complex-analysis facts (flagged in inventory as mathlib candidates); upstream. |

---

## Priority summary (highest leverage first)

1. **`analyticAt_cuspFunction_of_eventuallyEq` + `cuspFunction_apply_zero_eq`** — kills the 4×
   glue block, halves the file's longest proof, 6 call sites today, every future cusp-analyticity
   proof tomorrow.
2. **`laurentqExpansion_pow` / `laurentqExpansion_polynomial_eval₂` (+ `meromorphicAt_…_polynomial_eval`)**
   — deletes two ~40-line duplicated inductions in IntegralDescent/DiagonalLaurent and completes
   the ring-hom story of `laurentqExpansion`.
3. **`poleOrder_eq_of_meromorphicOrderAt_eq` + `analyticOrderAt_const_mul_pow`** — the two
   lemmas jointly collapse `poleOrder_coxAction_aux` (54→~15), `j_poleOrder`,
   `meromorphicOrderAt_cuspFunction_nat_mul`, `poleOrder_nat_mul`.
4. **Single `jIntCoeff` + `LaurentSeries` integrality layer (`laurentSeriesMapRingHom_ofPowerSeries` square)**
   — unifies 3 coefficient extractions and 2 integrality formalisations spanning 6 files.
5. **`CoxMatrix.ext` + `CoxMatrix.ofColumnHNF`** — structural ergonomics for the whole
   CoxMatrices/HNF cluster (4 injectivity proofs, 2 duplicated construction blocks).
6. `cuspFunction_eventuallyEq_eval` transfer lemma; `IsGamma0ModularFunction` closure set;
   `UpperHalfPlane.natScale`; simp set for `laurentqExpansion.coeff_*` and
   `BivariatePolynomial`; LevelThree jet-machinery generalisation; naming/duplicate cleanup in
   `LaurentQExpansion.lean` (2 exact duplicates, 2 over-generic root names).
