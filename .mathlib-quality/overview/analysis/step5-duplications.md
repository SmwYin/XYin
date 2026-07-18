# Step 5 — Duplication detection

All candidate pairs were verified against source (not just inventory descriptions). Paths are
relative to `/Users/dfa25dxu/Projects/Lean/XYin/`. Line numbers are from the working tree on
branch `PhD_Experiment` (2026-07-17).

## Pairwise comparison table

| # | Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|--------|--------|-----------------|-------------|---------|
| 1 | `exists_coxMatrix_reduction` (CoxMatrices/Basic.lean:403) | `exists_sl_right_mul_isColumnHermiteNormalForm_aux` + `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (Basic.lean:889, 904) | A = composition of B's two parts | σ-construction block 429–461 is char-for-char identical to 912–938; SL₂-upgrade block 406–427 duplicates 892–902 | DERIVE (keep the two general aux lemmas, reprove A as a 6-line corollary) |
| 2 | `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (LaurentQExpansion/LaurentQExpansion.lean:662) | `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` (same file:593) | YES — identical, both take `h0 : poleOrder h f ≠ 0` | A's proof is literally `exact B` | DELETE-ONE (keep the un-suffixed name) |
| 3 | `cuspFunction_to_analyticAt_analyticAt` (LaurentQExpansion.lean:793) | `analyticAt_cuspFunction_poleRemoved` (same file:322) | YES — identical | A's proof is `exact B` | DELETE-ONE (keep B, mathlib-style name) |
| 4 | `cuspFunction_to_analyticAt_meromorphicAt` (LaurentQExpansion.lean:788) | `(analyticAt_cuspFunction_poleRemoved …).meromorphicAt` | A is B + one projection | one-line wrapper | DELETE-ONE (inline `.meromorphicAt` at call sites; zero external uses) |
| 5 | `polynomial_prod_coeff_mdifferentiable_aux` (ModularPolynomial/Interpolation.lean:186) | `polynomial_prod_coeff_cuspMeromorphicAt` (ModularPolynomial/AnalyticSupport.lean:69) | Same shape, predicate differs (MDiff vs MeromorphicAt cuspFunction) | Identical `Finset.induction_on` skeleton (empty→coeff_one split; insert→coeff_mul + sum + mul closure) | EXTRACT-HELPER |
| 6 | `coxRoot_mdifferentiable_aux` / `coxLinearFactor_coeff_mdifferentiable_aux` (Interpolation.lean:165, 171) | `coxRoot_cuspMeromorphicAt` / `coxLinearFactor_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:33, 40) | Same shape, predicate differs | Identical case split on n (0 / 1 / ≥2) | EXTRACT-HELPER (same fix as #5) |
| 7 | `symmetricCubicExpansion_coeff_zero/one/two/three` (Cox/SymmetricCubicLaurent.lean:44, 63, 82, 101) | each other | Identical up to the literal index 0/1/2/3 | Char-for-char identical | UNIFY (one lemma `symmetricCubicExpansion_coeff (i : ℕ) (hi : i ≤ 3)`) |
| 8 | `foo` (qExpansion_tactic/Qj.lean:178) | `deltaFoo` (Qj.lean:208) | Same meta routine, differs only in 3 constant names (qjCoeffInt/qj_qexpansion/qj_qexpansion_coeff_eq ↔ delta versions) | Identical line-for-line | UNIFY |
| 9 | `fooWithValue` (Qj.lean:195) | `deltaFooWithValue` (Qj.lean:225) | ditto | Identical | UNIFY (same fix as #8) |
| 10 | `foo` (Qj.lean:178) | `fooWithValue` (Qj.lean:195) | A computes the value B receives; rest identical | 80 % shared body | UNIFY (one def with `Option Q(ℤ)` value) |
| 11 | Δ-table fold in `deltaCoeffsArrayUpTo` (Qj.lean:58–66) | same fold inlined in `qoverDeltaCoeffsArrayUpTo` (74–89) and `qjCoeffsArrayUpTo` (94–110) | Same computation ×3 | Copy-pasted `(e4Cube − e6Sq)/1728` fold | EXTRACT-HELPER |
| 12 | `qoverDeltaCoeffsArrayUpTo` (Qj.lean:74) | `qjCoeffsArrayUpTo` (Qj.lean:94) | B = A + one final `convArrayUpTo` | Lines 95–109 duplicate 75–89 verbatim | EXTRACT-HELPER (same fix as #11) |
| 13 | `Delta_qExpansion_coeff_zero_aux` (jFunction/Deltaqexpansions.lean:92, private, **dead**) | inline `hcoeff0` proofs (jFunction/jfunction.lean:101, 130) | Same fact `(qExpansion 1 Delta).coeff 0 = 0` | Same `simpa [qExpansion_coeff] using CuspFormClass.cuspFunction_apply_zero …` | DELETE-ONE (promote the aux to public, use it at both inline sites) |
| 14 | test 4 (Tactic2/LaurentQExpSimpTests.lean:28–33) | test 5 (same file:35–40) | YES | Char-for-char identical | DELETE-ONE |
| 15 | `transformedJSeries` (Cox/CoxMatrices/LaurentExpansion.lean:50) | `cyclotomicTransformedJSeries` (Cox/Kronecker.lean:594) | Same series; phase `ζ^e` in a field vs `phasePolynomial p e` in `Polynomial ℤ` | Identical coefficient formula and identical isPWO support proof | UNIFY (parametrize the phase function) |
| 16 | `jIntCoeff` (CoxMatrices/LaurentExpansion.lean:31) | `qjCoeffs` (jFunction/jfunction.lean:393) | Same integers, ℤ-indexed vs ℕ-indexed, both choice-based | Independent `choose` definitions; no bridging lemma between them | DERIVE (make `jIntCoeff` canonical; see action 9) |
| 17 | `jIntCoeff` | `qjCoeffInt` (qExpansion_tactic/Qj.lean:112, computable) | Same integers (`jIntCoeff (n−1) = qjCoeffInt n`) | Bridge exists but is **private and 3-specific**: `jIntCoeff_eq_qjCoeffInt_three` (Cox/LevelThree.lean:122) despite not depending on 3 | DERIVE (publish the general bridge) |
| 18 | `jIntegralLaurentSeries` (Cox/Kronecker.lean:160) | `jIntCoeff` | Packaging of the same coefficients as a LaurentSeries | n/a | DISTINCT (legitimate packaging; keep) |
| 19 | `integralDelta`/`ramanujanTau` (Deltaqexpansions.lean:394, 397; choice-based) | `Delta_qexpansion`/`deltaCoeffInt` (Qj.lean:160, 68; computable) | Same series/coefficients, bridged by `ramanujanTau_link`, `Delta_qexpansion_link` (link.lean:248, 213) | Parallel stacks by design (native_decide needs the computable one) | DISTINCT (intentional twin, bridges exist — but see action 9 note) |
| 20 | E4-side lemmas ×8 (Deltaqexpansions.lean: `E4_qExpansion_coeff_aux`:41, `E4_isIntegralPowerSeries`, `integralE4_coeff_dvd_aux`, `integralE4_coeff_zero`, `integralE4_constantCoeff_aux`, `integralE4_coeff_of_pos`:164, `e4Bar_coeff_dvd_aux`, `integralE4`) | E6-side mirrors (`E6_…`, `integralE6_…`, `e6Bar_…`) | Mirror statements (k=4↔6, 240↔−504, σ₃↔σ₅) | Identical proofs modulo those constants | EXTRACT-HELPER (one `toIntegralPowerSeries_coeff_eq` transfer lemma collapses 6 of the 8 pairs) |
| 21 | `complex_mobius_scale_eq_affine` (Cox/ModularFunction.lean:223, private) | same name (Cox/CoxMatrices/Basic.lean:797, private) | YES | Char-for-char identical (Basic imports ModularFunction) | DELETE-ONE (un-private the upstream copy) |
| 22 | `periodic_comp_ofComplex_of_vadd` (ModularFunction.lean:66, private) | `periodic_comp_ofComplex_of_vadd_aux` (CoxMatrices/LaurentExpansion.lean:93, private) | YES | Char-for-char identical | DELETE-ONE (un-private upstream) |
| 23 | `j_periodic` (ModularFunction.lean:151, public) | `j_periodic_aux` (CoxMatrices/LaurentExpansion.lean:109, private) | YES | Same 4-line proof; the public one is already importable at the aux's site | DELETE-ONE |
| 24 | `j_mdifferentiable_aux` (Cox/LatticeJ.lean:641, private) | `j_mdifferentiable` (Cox/ModularFunction.lean:136, public; MF imports LatticeJ) | YES | Same proof re-typed downstream | DELETE-ONE (make LatticeJ's copy the public `j_mdifferentiable`, drop MF's) |
| 25 | `cuspFunction_mul_eventuallyEq` (LaurentQExpansion.lean:54, private) | same name (ModularFunction.lean:876, private) | YES | Char-for-char identical | DELETE-ONE (un-private upstream) |
| 26 | `rankTwoContent_dvd_entry_aux`, `dvd_rankTwoContent_aux`, `rankTwoContent_dvd_mul_right_aux` (CoxMatrices/Basic.lean:234, 244, 248) | `Matrix.rankTwoContent_dvd_entry`, `dvd_rankTwoContent`, `rankTwoContent_dvd_mul_right` (Cox/HermiteNormalForm.lean:47, 61, 65 — **private**) | YES ×3 | Identical; re-proved only because the originals are private | DELETE-ONE ×3 (un-private the HNF originals) |
| 27 | `reduced_eq_of_eq_add_mul_aux` (CoxMatrices/Basic.lean:277) | `reduced_eq_of_eq_add_mul` (HermiteNormalForm.lean:269, private) | YES | Char-for-char identical | DELETE-ONE (un-private original) |
| 28 | `laurentqExpansion_j_order_aux`, `_leadingCoeff_aux`, `_pow_aux`, `_pow_order_aux`, `_pow_leadingCoeff_aux`, `polynomialIn_cuspMeromorphicAt_aux`, `laurentqExpansion_polynomialIn_j_aux` (ModularPolynomial/IntegralDescent.lean:24–92) | `laurentqExpansion_j_order_widthM`, `_leadingCoeff_widthM`, `_pow_widthM`, `_pow_order_widthM`, `_pow_leadingCoeff_widthM`, `polynomialIn_widthM_cuspMeromorphicAt`, `laurentqExpansion_polynomialIn_j_widthM` (Cox/DiagonalLaurent.lean:32–260) | A = h=1 special case of B (m=1) | Same proof skeletons (B is downstream of A, so A could not reuse B) | DERIVE (move the widthM versions upstream; the h=1 block becomes `simpa using X 1`) |
| 29 | `prime_sq_dvd_iff_dvd_shift_natAbs` (Cox/KroneckerFrobenius.lean:98) | `int_dvd_iff_dvd_add_natAbs` (Cox/LevelThree.lean:559, more general, but downstream and private) | A = B at d = p² (modulo `k − −(p²)` vs `k + d`) | Both short natAbs/dvd manipulations proved independently | UNIFY (general lemma upstream; `three/nine_dvd_iff…` LevelThree:569, 573 already derive correctly from it) |
| 30 | `coxPhiFunction_coeff_slashInvariant→widthM→widthOne→isLevelOne` pipeline (ModularPolynomial/Construction.lean:270–334) | `interpolation_coeff_slashInvariant_aux→widthM_aux→widthOne_aux→isLevelOne` pipeline (Interpolation.lean:299–330) | Same descent argument applied to two families | `widthOne` and `isLevelOne` steps are near-verbatim (e.g. Construction:300–306 ≡ Interpolation:309–317) | EXTRACT-HELPER |
| 31 | `HasIntegralQExpansion` (IntegralPowerSeries/HasIntegralQExpansion.lean:6) | `IsIntegralPowerSeries` (IntegralPowerSeries/IntegralPowerSeries.lean:135) | NO — A is ∃-shifted (`q^n·f`) integrality, meromorphic-friendly | different | DISTINCT (note: `HasIntegralQExpansion.sum` at line 29 contains a `sorry`) |
| 32 | `IsIntegralCPowerSeries` (IntegralPowerSeries.lean:104) | `IntegralPowerSeries.IsIntegralPowerSeries` (same file:135) | YES — both abbrevs unfold to `HasCoeffsIn ℤ ℂ` | n/a (abbrev chain) | DELETE-ONE (keep one name; `IsIntegralCPowerSeries` has ~no direct uses) |
| 33 | `QExpSimp.analyticAt_cuspFunction_mul/add/…` (Tactic2/qexp_simp.lean:55–) | `meromorphicAt_cuspFunction_mul/add/…` (LaurentQExpansion.lean:73–) | NO — AnalyticAt vs MeromorphicAt, and the QExpSimp proofs go through mathlib `cuspFunction_mul` | different | DISTINCT (tactic simp-set entries; keep) |
| 34 | `natCast_mul_im_pos_aux` (jFunction/jLevelN.lean:32) + inline `⟨N·τ, _⟩` in `jN` | `natScaleUpperHalfPlane` + `coe_natScaleUpperHalfPlane` (ModularFunction.lean:180, 187) | Both construct `N·τ : ℍ`; MF imports jLevelN | Independent constructions of the same object | EXTRACT-HELPER (one shared `UpperHalfPlane.natScale`) |
| 35 | `qjCoeffTableThree` (Cox/LevelThree.lean:42) | `qjCoeffInt` (Qj.lean:112) | Table of first 13 values vs computable def, linked by `decide +kernel` (`qjCoeffInt_eq_tableThree`:47) | n/a | DISTINCT (verified-value table is a legitimate pattern) |

**Totals: 35 rows — DELETE-ONE 14 · UNIFY 6 · DERIVE 4 · EXTRACT-HELPER 6 · DISTINCT 5.**

## Action items (non-DISTINCT rows)

### A1. CoxMatrix construction block (row 1)
`XYin/PhD/Cox/CoxMatrices/Basic.lean`. Move `exists_sl_right_mul_isColumnHermiteNormalForm_aux`
(889–902) and `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (904–938) **above** line 403 and
reprove:
```lean
private theorem exists_coxMatrix_reduction (m : ℕ+) (γ : SL(2, ℤ)) :
    ∃ (σ : CoxMatrix m) (U : SL(2, ℤ)), coxInput m γ * U.1 = σ.inclusionMatrix := by
  obtain ⟨U, hH⟩ := exists_sl_right_mul_isColumnHermiteNormalForm_aux (coxInput m γ)
    (by rw [coxInput_det]; positivity)
  obtain ⟨σ, hσ⟩ := exists_coxMatrix_of_isColumnHermiteNormalForm_aux (coxInput m γ * U.1) hH
    (by rw [Matrix.det_mul, coxInput_det]; simp) (by rw [rankTwoContent_mul_sl, coxInput_content_eq_one])
  exact ⟨σ, U, hσ⟩
```
Deletes ~55 duplicated lines.

### A2. Exact-duplicate lemmas in LaurentQExpansion.lean (rows 2–4)
- Delete `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` (593–610); keep its proof
  under the name `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (delete the wrapper at
  662–664). Update the one external use at `Cox/CoxMatrices/LaurentExpansion.lean:198`.
- Delete `cuspFunction_to_analyticAt_analyticAt` (793–796) and
  `cuspFunction_to_analyticAt_meromorphicAt` (788–791); use `analyticAt_cuspFunction_poleRemoved`
  (322) and `.meromorphicAt` at line 802 (only internal use).

### A3. Predicate-parametric product-coefficient closure (rows 5–6)
New helper in `ModularPolynomial/AnalyticSupport.lean` (or a small shared file):
```lean
theorem polynomial_prod_coeff_closure {ι : Type*} (p : (ℍ → ℂ) → Prop)
    (hconst : ∀ c : ℂ, p (fun _ ↦ c)) (hmul : ∀ {f g}, p f → p g → p (f * g))
    (hsum : ∀ {s : Finset _} {f}, (∀ i ∈ s, p (f i)) → p (∑ i ∈ s, f i))
    (P : ι → Polynomial (ℍ → ℂ)) (s : Finset ι)
    (hP : ∀ i ∈ s, ∀ n, p ((P i).coeff n)) : ∀ n, p ((s.prod P).coeff n)
```
Instantiate with `p := MDiff` (Interpolation.lean:186) and
`p := fun f ↦ MeromorphicAt (cuspFunction h f) 0` (AnalyticSupport.lean:69). Same treatment
collapses the `coxLinearFactor_coeff_*` twins (case split on n is identical).

### A4. symmetricCubicExpansion coefficient quadruplet (row 7)
`Cox/SymmetricCubicLaurent.lean:44–118` → one lemma
```lean
private theorem symmetricCubicExpansion_coeff {K} [CommRing K] (P : BivariatePolynomial K)
    (i : ℕ) (hi : i ≤ 3) (hinner : (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff i = P.coeff i := by
  interval_cases i <;> · apply Polynomial.ext; intro j; by_cases hj : j ≤ 3 <;> [skip; skip] …
```
(the existing proof body works verbatim for each branch). `eq_symmetricCubicExpansion` (120)
then calls it with `hi` from `interval_cases`. Deletes ~55 lines.

### A5. Qj meta-def quadruplet (rows 8–10)
`qExpansion_tactic/Qj.lean:178–235`. One parametric routine:
```lean
structure QexpTarget where
  coeffFn   : Name  -- ``qjCoeffInt / ``deltaCoeffInt
  seriesEq  : Name  -- ``qj_qexpansion_coeff_eq / ``Delta_qexpansion_coeff_eq
  series    : Name  -- ``qj_qexpansion / ``Delta_qexpansion
def mkQexpCoeffProof (t : QexpTarget) (n : Nat) (xQ? : Option Expr) : MetaM (Expr × Expr) := …
```
`foo`/`deltaFoo` become `mkQexpCoeffProof t n none`; the `WithValue` twins pass `some xQ`.
The elab_rules (243–279) dispatch on `which.getId` to a `QexpTarget` constant. 4 defs → 1.

### A6. Inline Δ-table triplication in Qj.lean (rows 11–12) — unblocks link.lean fragility
Extract in `Qj.lean`:
```lean
def deltaArrayUpTo (top : Nat) : Array Int := … -- the (e4Cube − e6Sq)/1728 fold, once
def deltaOverQArrayUpTo (n : Nat) : Array Int :=
  (List.range (n+1)).foldl (fun acc i => acc.push ((deltaArrayUpTo (n+1)).getD (i+1) 0)) #[]
```
then `deltaCoeffsArrayUpTo n := deltaArrayUpTo n`,
`qoverDeltaCoeffsArrayUpTo n := inverseOnePlusCoeffsUpTo (deltaOverQArrayUpTo n) n`,
`qjCoeffsArrayUpTo n := convArrayUpTo e4Cube (qoverDeltaCoeffsArrayUpTo n) n`.
Then `link.lean:366` `delta_array_getD` (whose statement currently spells out the whole inlined
fold) becomes a clean `deltaArrayUpTo_getD`, and `inverseOnePlusCoeffsUpTo_toList` (link.lean:324)
no longer needs to re-match a copy-pasted expression. Verify `native_decide` performance is
unchanged (same computation, one extra def indirection).

### A7. Dead `Delta_qExpansion_coeff_zero_aux` (row 13)
Make `Deltaqexpansions.lean:92` public (drop `private`, name `Delta_qExpansion_coeff_zero`), and
replace the inline `hcoeff0` proofs at `jfunction.lean:101` and `jfunction.lean:130` with it
(jfunction already imports Deltaqexpansions).

### A8. Test duplicate (row 14)
Delete lines 35–40 of `Tactic2/LaurentQExpSimpTests.lean` (test 5 ≡ test 4).

### A9. The "integer coefficients of j" family (rows 15–19) — canonical-notion map
Current parallel notions:
- `jIntCoeff : ℤ → ℤ` (CoxMatrices/LaurentExpansion.lean:31, choice from `j_laurentQExpansion_isIntegral`) — used by the whole Cox chain (29 refs).
- `qjCoeffs : ℕ → ℤ` (jfunction.lean:393, choice from `qj_isIntegralPowerSeries`) — 35 refs, jFunction side.
- `qjCoeffInt : ℕ → ℤ` (Qj.lean:112, computable) — native_decide ground truth.
- `jIntegralLaurentSeries` (Kronecker.lean:160) — packaging of `jIntCoeff` (fine).

**Proposed canonical**: `jIntCoeff` (ℤ-indexed, matches the Laurent expansion that everything
downstream consumes). Concretely:
1. Move `def jIntCoeff` + `jIntCoeff_spec` + `jIntCoeff_neg_one` into `jfunction.lean` right
   after `j_laurentQExpansion_isIntegral` (its only prerequisite), re-export from
   CoxMatrices/LaurentExpansion.
2. Add the bridge `qjCoeffs n = jIntCoeff ((n : ℤ) - 1)` (provable by ℂ-cast injectivity via
   `qj_coeff_cast_aux` + `laurentqExpansion.coeff_of_geq`, exactly the argument already inside
   `qexp_coeffs.lean:j_laurentQExpansion_coeff_eq_qj_coeff_aux`) — or eliminate `qjCoeffs`
   outright by redefining it as that expression.
3. Generalize and publish the private, 3-specific bridge `jIntCoeff_eq_qjCoeffInt_three`
   (LevelThree.lean:122) as `jIntCoeff_eq_qjCoeffInt (n : ℕ) : jIntCoeff ((n:ℤ)-1) = qjCoeffInt n`
   in `qExpansion_tactic/link.lean` (its proof never uses 3). LevelThree then gets it for free,
   and any future LevelN file will not have to re-prove it.
The computable twins (`qjCoeffInt`, `deltaCoeffInt`, `Delta_qexpansion`) stay — they are the
native_decide layer — but every *noncomputable* notion should be `jIntCoeff`-derived.

### A10. transformedJSeries vs cyclotomicTransformedJSeries (row 15)
Generalize `CoxMatrices/LaurentExpansion.lean:50` to
```lean
noncomputable def phasedJSeries {K : Type*} [CommRing K] {m : ℕ+}
    (phase : ℤ → K) (σ : CoxMatrix m) : LaurentSeries K :=
  ⟨fun k ↦ if (σ.a : ℤ)^2 ∣ k ∧ -((σ.a : ℤ)^2) ≤ k
      then (jIntCoeff (k / (σ.a:ℤ)^2) : K) * phase (((σ.a:ℤ) * σ.b) * (k / (σ.a:ℤ)^2)) else 0,
   -- support proof unchanged (verbatim from the current def)⟩
```
`transformedJSeries ζ σ := phasedJSeries (ζ ^ ·) σ` (Field K),
`cyclotomicTransformedJSeries p σ := phasedJSeries (phasePolynomial p) σ` (Kronecker.lean:594).
The two identical isPWO proofs collapse to one, and `cyclotomicTransformedJSeries_map_complex/_map_mod`
become instances of a single `phasedJSeries_map` lemma.

### A11. E4/E6 mirror machinery (row 20)
Add to `IntegralPowerSeries/IntegralPowerSeries.lean`:
```lean
lemma toIntegralPowerSeries_coeff_eq {S : PowerSeries ℂ} (h : IsIntegralPowerSeries S)
    {n : ℕ} {z : ℤ} (hz : S.coeff n = (z : ℂ)) : (toIntegralPowerSeries h).coeff n = z
```
(proof: `congrArg` + `coeTo_of_toIntegralPowerSeries` + cast injectivity — the exact 4 lines
currently repeated in `integralE4_coeff_zero`, `integralE6_coeff_zero`,
`integralE4/6_constantCoeff_aux`, `integralE4/6_coeff_of_pos` (Deltaqexpansions.lean:164–178),
and again in `qexp_coeffs.lean`). The `E4/E6_qExpansion_coeff_aux` pair stays (genuinely different
Bernoulli constants) but the 6 downstream mirror pairs each become one-liners.

### A12. Cross-file private re-proofs (rows 21–27) — un-private upstream, delete downstream
| Keep (make public) | Delete |
|---|---|
| `complex_mobius_scale_eq_affine` — ModularFunction.lean:223 | CoxMatrices/Basic.lean:797–~830 |
| `periodic_comp_ofComplex_of_vadd` — ModularFunction.lean:66 | CoxMatrices/LaurentExpansion.lean:93–107 (`_aux`) |
| `j_periodic` — ModularFunction.lean:151 (already public) | CoxMatrices/LaurentExpansion.lean:109–113 (`j_periodic_aux`) |
| `j_mdifferentiable` — move to Cox/LatticeJ.lean:641 (drop `private`/`_aux`) | ModularFunction.lean:136–150 duplicate |
| `cuspFunction_mul_eventuallyEq` — LaurentQExpansion.lean:54 | ModularFunction.lean:876–884 |
| `Matrix.rankTwoContent_dvd_entry`, `dvd_rankTwoContent`, `rankTwoContent_dvd_mul_right` — HermiteNormalForm.lean:47, 61, 65 | CoxMatrices/Basic.lean:234–258 (`*_aux` ×3) |
| `reduced_eq_of_eq_add_mul` — HermiteNormalForm.lean:269 | CoxMatrices/Basic.lean:277–283 (`_aux`) |
These are all char-for-char copies that exist only because the upstream original is `private`.
~120 lines deleted; no statement changes.

### A13. h=1 vs width-m Laurent-of-j block (row 28)
The 7 `*_widthM` lemmas (Cox/DiagonalLaurent.lean:27–260) generalize the 7 `*_aux` lemmas
(ModularPolynomial/IntegralDescent.lean:24–92), but live downstream. Move the widthM versions
into `ModularPolynomial/IntegralDescent.lean` (their proofs only need `laurentqExpansion_nat_mul_coeff`
from LaurentQExpansion/Algebra + `j_isGamma0ModularFunction` from ModularFunction — both already
imported there). Then each h=1 aux becomes e.g.
`laurentqExpansion_j_order_aux := by simpa using laurentqExpansion_j_order_widthM 1`
(`((1:ℕ+):ℕ):ℝ = 1` by `Nat.cast_one`/`PNat.one_coe`). DiagonalLaurent keeps only re-exports.

### A14. natAbs-divisibility shift lemmas (row 29)
Move `int_dvd_iff_dvd_add_natAbs` (LevelThree.lean:559) upstream (e.g. into Kronecker.lean or a
small arithmetic prelude), un-private it, and replace `prime_sq_dvd_iff_dvd_shift_natAbs`
(KroneckerFrobenius.lean:98) by
`(by simpa [sub_neg_eq_add] using int_dvd_iff_dvd_add_natAbs ((p:ℕ)^2) k : …)`.
`three/nine_dvd_iff_dvd_shift_natAbs` already derive from it and are fine.

### A15. Level-one descent pipeline (row 30)
Extract into `Cox/ModularFunction.lean` (or AnalyticSupport):
```lean
theorem isLevelOne_of_slashInvariant_of_mdiff_of_widthM {m : ℕ+} {g : ℍ → ℂ}
    (hslash : ∀ δ : SL(2,ℤ), g ∣[(0:ℤ)] δ = g) (hmd : MDiff g)
    (hwidth : MeromorphicAt (cuspFunction ((m:ℕ):ℝ) g) 0) :
    IsLevelOneModularFunction g
```
(body = the current Construction.lean:300–334 argument: `meromorphicAt_cuspFunction_of_nat_mul` +
`periodic_comp_of_slashInvariant_one` + meromorphicOnH from MDiff). Both
`coxPhiFunction_coeff_isLevelOne` (Construction.lean:320) and `interpolation_coeff_isLevelOne`
(Interpolation.lean:321) reduce to 3-line applications; the private `*_widthOne_*` and
`*_meromorphicOnH_*` steps in both files disappear.

### A16. Redundant abbrev (row 32)
`IntegralPowerSeries/IntegralPowerSeries.lean`: collapse the abbrev chain
`IsIntegralCPowerSeries` (104) ≡ `IsIntegralPowerSeries` (135) to a single name (keep
`IsIntegralPowerSeries`, the one used project-wide; delete or deprecate the other).

## Notes surfaced during verification
- `HasIntegralQExpansion.sum` (IntegralPowerSeries/HasIntegralQExpansion.lean:29) contains a
  `sorry` — flag for the sorry-tracking step.
- `Deltaqexpansions.lean` and several Cox files carry a doubled copyright header
  (DiagonalLaurent.lean:1–10) — style step.
- `LaurentQExpSimpTests.lean` never uses the `qexp_simp` tactic despite its name (tests the
  LaurentQExpansion API directly) — naming/organization step.
