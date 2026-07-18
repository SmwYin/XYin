# Step 4 — Mathlib-API audit: Cox matrices, modular polynomial, function fields

Files audited (full source read): `CoxMatrices/{Basic,Cardinality,LaurentExpansion}.lean`,
`FormalCoxProduct.lean`, `UpperHalfPlaneFunctionField.lean`,
`ModularPolynomial/{Construction,AnalyticSupport,Interpolation,Irreducibility,IntegralDescent}.lean`,
`ModularFunction.lean`, `ModularFunctionField.lean`, `Arithmetic.lean`.
All cited mathlib names below were verified by grep against
`.lake/packages/mathlib/Mathlib` (paths given per finding).

---

## Definitions to Replace with Mathlib

**`eval_derivative_prod_X_sub_C_at` (Interpolation.lean) → replace with `Lagrange` nodal API** —
Current: 25-line private proof that
`(derivative (∏ k, (X - C (r k)))).eval (r i) = ∏ k ∈ univ.erase i, (r i - r k)`.
Mathlib alternative (verified, `Mathlib/LinearAlgebra/Lagrange.lean`, Nodal section, works over any
`CommRing`): `Lagrange.nodal`, `Lagrange.nodal_eq` (`nodal s v = ∏ i ∈ s, (X - C (v i))`),
`Lagrange.eval_nodal_derivative_eval_node_eq` (`eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v)`),
`Lagrange.eval_nodal` (`(nodal s v).eval x = ∏ i ∈ s, (x - v i)`), plus `Lagrange.derivative_nodal`.
The lemma is literally the composition of `eval_nodal_derivative_eval_node_eq` and `eval_nodal` at
`s = Finset.univ`. Impact: deletes a whole proof; also `modularDerivativeHolomorphic` and
`recoveryFormula` denominators could be phrased through `Lagrange.nodal`/`Lagrange.nodalWeight`.
**Action**: rewrite the products `∏ (X - C (j (σ.act τ)))` as `Lagrange.nodal Finset.univ (fun σ ↦ j (σ.act τ))`
locally, replace the private lemma by the two mathlib lemmas. Difficulty: easy.

**`transformedJSeries` (LaurentExpansion.lean) → build with `HahnSeries.ofSuppBddBelow`** —
Current: anonymous-constructor `HahnSeries` with a manual `Set.IsWF.isPWO`/`BddBelow.isWF`
support proof (note `BddBelow.isWF` was recently renamed in mathlib — a deprecation alias
dated 2026-01-02 exists at `RingTheory/HahnSeries/Basic.lean:567`).
Mathlib alternative (verified `RingTheory/HahnSeries/Basic.lean:574,589`):
`HahnSeries.ofSuppBddBelow (f) (hf : BddBelow (Function.support f))` with
`HahnSeries.coeff_ofSuppBddBelow : (ofSuppBddBelow f hf).coeff = f`.
Impact: the PWO boilerplate disappears and `transformedJSeries_coeff` becomes
`coeff_ofSuppBddBelow`-rewriting. **Action**: define
`transformedJSeries ζ σ := HahnSeries.ofSuppBddBelow (fun k ↦ if … then … else 0) ⟨-(σ.a^2), …⟩`.
Difficulty: easy.

**`constant` (UpperHalfPlaneFunctionField.lean) → `Pi.constRingHom` + `RingHom.codRestrict`** —
Current: hand-assembled `ℂ →+* HolomorphicFunction` with four `rfl` fields.
Mathlib alternative (verified `Algebra/Ring/Pi.lean:167`): `Pi.constRingHom ℍ ℂ : ℂ →+* (ℍ → ℂ)`;
compose with `RingHom.codRestrict _ holomorphicFunctions (fun _ ↦ mdifferentiable_const)`.
Impact: minor; removes a bespoke hom and makes `constant` defeq-transparent to mathlib simp
lemmas about `Pi.constRingHom`. **Action**: redefine `constant`. Difficulty: trivial.

**`matrixStar` (CoxMatrices/Basic.lean) → express through `submatrix`/`transpose` (or `adjugate`)** —
Current: `!![A 1 1, A 0 1; A 1 0, A 0 0]` with three `fin_cases`-proved lemmas
(`matrixStar_involutive`, `matrixStar_mul`, `matrixStar_det`).
Mathlib alternative: `matrixStar A = (A.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1))ᵀ`;
then `matrixStar_det` follows from `Matrix.det_submatrix_equiv_self`
(verified `LinearAlgebra/Matrix/Determinant/Basic.lean:223`) + `Matrix.det_transpose`, and
`matrixStar_mul` from `Matrix.transpose_mul` + `Matrix.submatrix_mul_equiv`
(verified `Data/Matrix/Mul.lean:1161`). Alternatively `matrixStar A = D * adjugate A * D` with
`D = diagonal ![1,-1]`, using `Matrix.adjugate_fin_two`/`Matrix.adjugate_mul_distrib`
(verified `LinearAlgebra/Matrix/Adjugate.lean:373,455`).
Impact: replaces entry-chasing with structural lemmas; `matrixStar` stays private either way.
**Action**: optional refactor; keep the current statement forms as `simp` corollaries.
Difficulty: easy–medium (low payoff; the current proofs are short).

---

## API Choice Improvements

**`CoxMatrix.act` (CoxMatrices/Basic.lean) → route through mathlib's `MulAction (GL (Fin 2) ℝ) ℍ`** —
Current: `act` builds the point `((a·τ + b)/d : ℍ)` by hand, including a 10-line positivity proof
of the imaginary part, and `levelJ_smul_eq_j_act_of_normalization` re-derives Möbius composition
arithmetic via the bespoke `complex_mobius_scale_eq_affine`.
Mathlib alternative (all verified in `Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`):
`UpperHalfPlane.glAction : MulAction (GL (Fin 2) ℝ) ℍ` (line 188),
`Matrix.GeneralLinearGroup.mkOfDetNeZero` (`LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean:116`),
`UpperHalfPlane.coe_smul_of_det_pos` (line 198), `UpperHalfPlane.glPos_smul_def` (line 207).
`σ.mobiusMatrix` has determinant `m ≠ 0`, so
`act σ τ := (Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.mobiusMatrix.map (Int.cast : ℤ → ℝ)) _) • τ`
gives `coe_act` from `coe_smul_of_det_pos` and — more importantly — composition laws
(`mul_smul`) for free, which would shorten the coset-translation bookkeeping
(`rightCosetEval_smul`, `levelJ_smul_eq_j_act_of_normalization`).
**Action**: consider redefining `act` as a GL-smul and proving the current `coe_act` as the bridge
lemma. Difficulty: medium (touches many downstream files; do only if the Möbius arithmetic keeps
recurring).

**`natScaleUpperHalfPlane` (ModularFunction.lean) and inline `zN`/scaled points (Basic.lean:823) →
`UpperHalfPlane.posRealAction`** — Current: two independent hand-rolled "multiply a point of ℍ by a
positive natural" constructions with manual `Complex.mul_im` positivity proofs. Mathlib alternative
(verified `Analysis/Complex/UpperHalfPlane/Basic.lean:197`):
`instance posRealAction : MulAction {x : ℝ // 0 < x} ℍ` — `(⟨(N:ℝ), by positivity⟩ : {x // 0 < x}) • τ`.
`affineUpperHalfPlane` in the same file already uses exactly this action, so the file is internally
inconsistent. **Action**: define `natScaleUpperHalfPlane N τ := (⟨(N:ℝ), _⟩ : {x : ℝ // 0 < x}) • τ`
and reuse in Basic.lean. Difficulty: easy.

**`IsGamma0ModularFunction` (ModularFunction.lean) → structure with named fields** —
Current: a `Prop` triple accessed everywhere as `hf.1`, `hf.2.1`, `hf.2.2` (dozens of call sites in
Construction/Interpolation/AnalyticSupport). Mathlib design (cf. `SlashInvariantForm`,
`ModularForm` in `NumberTheory/ModularForms/`) is structures with named fields; there is **no**
meromorphic modular-function class in mathlib to reuse (verified: nothing meromorphic under
`Mathlib/NumberTheory/ModularForms/`), so the predicate must stay project-side, but
`structure IsGamma0ModularFunction … where meromorphicOn : …; slashInvariant : …; cuspMeromorphic : …`
(or at least field-projection lemmas) would make every `.2.2 γ` self-documenting. The slash-action
interface (`f ∣[(0:ℤ)] γ`) is already the correct mathlib API. **Action**: introduce named
projections (`IsGamma0ModularFunction.meromorphicOn/slashInvariant/cuspMeromorphic`) even if the
`And`-shape is kept for `constructor` convenience. Difficulty: easy (mechanical).

**`BivariatePolynomial.eval` (Construction.lean) — argument-flip wrapper over `Polynomial.evalEval`** —
Current: `eval Φ x y := Φ.evalEval y x`, deliberately compensating mathlib's inner-first order.
Mathlib's `Algebra/Polynomial/Bivariate.lean` is rich (`evalEval_mul/prod/pow/finsetSum`,
`evalEvalRingHom`, `aevalAeval`, `coe_aevalAeval_eq_evalEval`, `eval₂_evalRingHom` — all verified),
and half of the project (Interpolation, ModularFunctionField, ModularFunction's `RationalInTwo`)
already uses raw `evalEval` while Construction/Arithmetic use the flipped `eval`. Two evaluation
conventions for the same object in one development is a real hazard (`modularPolynomialC_eval_levelJ_j`
vs `modularPolynomialC_eval_j_levelJ` differ only in the flip). **Action**: pick one convention;
preferably drop `BivariatePolynomial.eval` and standardise on `evalEval` with mathlib's order,
documenting "outer = Cox's X" once. Difficulty: medium (renames across 4 files, purely mechanical).

**`formalCoxPolynomial_map` / `formalCoxPolynomial_coeff_fixed` (FormalCoxProduct.lean) —
factor the inline `LaurentSeries` map RingHom** — Current: the anonymous
`{ toFun := fun F ↦ F.map φ, map_zero' := HahnSeries.map_zero …, … }` RingHom is spelled out
**twice** verbatim. Mathlib has `HahnSeries.map` (FunLike, accepts a `RingHom` directly;
`RingTheory/HahnSeries/Basic.lean:143`) and `HahnSeries.embDomainRingHom` (domain side), but no
bundled coefficient-side `mapRingHom` — a genuine mathlib gap. **Action**: define once
`private def LaurentSeries.mapRingHom (φ : K →+* L) : LaurentSeries K →+* LaurentSeries L` and use
it in both places (and in IntegralDescent, see next item); consider upstreaming as
`HahnSeries.mapRingHom`. Difficulty: easy.

**`integralLaurentSeries` (FormalCoxProduct.lean) vs `integerCoeffLaurentSeries`
(IntegralDescent.lean) — near-duplicate subrings** — Current: two private `Subring (LaurentSeries K)`
definitions with identical five-field proofs, one via `IsIntegral ℤ (F.coeff k)`, one via
`F.coeff n ∈ (Int.castRingHom ℂ).range`. Mathlib has no "coefficientwise subring" for
`HahnSeries` (verified). But a single parametrised project def
`coeffSubring (S : Subring K) : Subring (LaurentSeries K)` (membership `∀ n, F.coeff n ∈ S`) covers
the second directly and the first via the subring `integralClosure ℤ K` (mathlib
`integralClosure` is a `Subalgebra`, `.toSubring` works). Alternatively, `integerCoeffLaurentSeries`
is exactly the range of the bundled `LaurentSeries.mapRingHom (Int.castRingHom ℂ)` (coefficientwise
preimages keep the same support), i.e. `RingHom.range` gives the subring structure for free.
**Action**: unify into one def; five subring-axiom proofs deleted. Difficulty: easy.

**`gamma0RightCosetsFintype` (CoxMatrices/Basic.lean) — correct API, minor golf** — Verified the
chain used is the best available: `CongruenceSubgroup.instFiniteIndexGamma0` (mathlib,
`NumberTheory/ModularForms/CongruenceSubgroups.lean:206`), `Subgroup.fintypeQuotientOfFiniteIndex`
(`GroupTheory/Index.lean:707`), `QuotientGroup.quotientRightRelEquivQuotientLeftRel`
(`GroupTheory/Coset/Defs.lean:130`). No change needed beyond possibly `Fintype.ofEquiv` inlining.

---

## Hand-Rolled Patterns to Replace

**`rankTwoContent_dvd_entry_aux` / `dvd_rankTwoContent_aux` / `rankTwoContent_dvd_mul_right_aux`
(CoxMatrices/Basic.lean) → verbatim re-proofs of private lemmas in HermiteNormalForm.lean** —
`HermiteNormalForm.lean:47-80` already contains `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`,
`rankTwoContent_dvd_mul_right` (and even a `_left` variant) — but marked `private`, so Basic.lean
re-proves all three as `_aux`. **Action**: make the HermiteNormalForm lemmas public (they are the
natural home) and delete the `_aux` copies; while there, `rankTwoContent` itself could be
`Finset.univ.gcd (fun p : Fin 2 × Fin 2 ↦ (A p.1 p.2).natAbs)` so that `Finset.gcd_dvd` /
`Finset.dvd_gcd` replace the entry-chasing. Difficulty: trivial (publicize) / easy (Finset.gcd).

**`j_periodic_aux` + `periodic_comp_ofComplex_of_vadd_aux` (LaurentExpansion.lean) → duplicates of
ModularFunction.lean's `j_periodic` (public!) and `periodic_comp_ofComplex_of_vadd` (private)** —
LaurentExpansion imports `CoxMatrices.Basic`, which imports `ModularFunction`, so the public
`Cox.j_periodic` was already in scope; `periodic_comp_ofComplex_of_vadd` only needs to be made
public. **Action**: delete both `_aux` lemmas in LaurentExpansion, publicize the vadd lemma.
Difficulty: trivial.

**`complex_mobius_scale_eq_affine` — duplicated verbatim** in CoxMatrices/Basic.lean:797 and
ModularFunction.lean:223 (both `private`, identical statement and proof). **Action**: keep one
public copy (ModularFunction.lean is upstream of Basic.lean in the import graph) and delete the
other. Difficulty: trivial.

**`polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport.lean) vs
`polynomial_prod_coeff_mdifferentiable_aux` (Interpolation.lean)** — same induction skeleton
(`Finset.induction_on` + `Polynomial.coeff_mul` + closure of a predicate under
sum/mul/const) instantiated for two predicates. A single lemma
"`(∀ i ∈ s, ∀ n, P ((f i).coeff n)) → ∀ n, P ((s.prod f).coeff n)` for `P` a subring-closed
predicate" (take `P`-closure as a `Subring (ℍ → ℂ)` membership) would serve both. **Action**:
optional dedup via a `Subring`-membership formulation. Difficulty: easy.

**`exists_coprime_add_mul_of_gcd_gcd_eq_one` (CoxMatrices/Basic.lean)** — searched
`Data/Nat/GCD`, `RingTheory/Coprime`, `Data/Int/GCD`: mathlib has the *iff* forms
(`Nat.coprime_add_mul_right_right` etc.) but **no** existence lemma
`gcd (gcd a b) d = 1 → ∃ x, Coprime a (b + x*d)` (the CRT/Dirichlet shift trick). Hand-rolled is
justified; strong `mathlibable` candidate. No change.

**`card_le_minpoly_natDegree_of_injective_roots` / `irreducible_of_card_conjugates`
(Irreducibility.lean)** — verified they are built on exactly the right mathlib primitives:
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (`Algebra/Polynomial/Roots.lean:713`),
`minpoly.dvd`, `minpoly.monic`, `minpoly.irreducible`,
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (`FieldTheory/Minpoly/Field.lean` usage confirms),
`minpoly.aeval_algHom`. No mathlib lemma packages "monic + root + ≥ deg-many injective conjugate
roots of the minpoly ⇒ irreducible". Keep; both are clean general-field-theory statements and prime
`mathlibable` candidates (they mention nothing Cox-specific). No change.

**`hasse_qExpansion_principle` (IntegralDescent.lean)** — the leading-coefficient strong induction
via `Polynomial.eraseLead` is the standard mathlib idiom
(`eraseLead_add_monomial_natDegree_leadingCoeff`, `eraseLead_natDegree_le` — both used); the final
lift correctly uses `Polynomial.lifts_iff_coeff_lifts` / `Polynomial.exists_support_eq_of_mem_lifts`.
No mathlib replacement exists (Hasse q-expansion principle is not in mathlib). No change.

**`rightCosetMul` (CoxMatrices/Basic.lean)** — checked `GroupTheory/Coset/*`,
`GroupTheory/GroupAction/Quotient.lean`: mathlib has **no** `MulAction` (of `G` or `Gᵐᵒᵖ`) on
`Quotient (QuotientGroup.rightRel s)`; the only right-coset infrastructure is
`quotientRightRelEquivQuotientLeftRel`. The hand-rolled `Equiv` is appropriate. Optional: package
`rightCosetMul` as a `MulAction (SL(2,ℤ))ᵐᵒᵖ (Gamma0RightCosets m)` to get `mul_smul` laws, but
nothing downstream needs them. No change.

**`columnHNF_eq_of_mul` (CoxMatrices/Basic.lean)** — Hermite-normal-form uniqueness under right
unimodular equivalence. Mathlib has no Hermite normal form at all (verified: only Hermite
*polynomials* match a repo-wide grep). Correctly hand-rolled, but it belongs in
`HermiteNormalForm.lean` next to `IsColumnHermiteNormalForm`, not in the Cox-matrix file — as do
`exists_sl_right_mul_isColumnHermiteNormalForm_aux` and
`exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (the latter is 60% a copy of the σ-construction
inside `exists_coxMatrix_reduction`; the two should share one lemma). **Action**: move + dedup.
Difficulty: easy.

---

## Missing tags/instances

**`CoxMatrix` — missing `@[ext]` lemma** — Four different files re-derive extensionality by hand:
`toFin_injective`'s `cases/cases/simp_all` (Basic), `CoxMatrix.inclusionMatrix_injective` (Basic),
`reindex_bijective`'s `Prod.ext`+`Fin.ext` chain (LaurentExpansion), `transformed_injective`'s
`toFin` roundtrip (UpperHalfPlaneFunctionField), plus `coxMatrixEquivFiberSigmaAux.left_inv`
(Cardinality). **Action**: add
`@[ext] theorem CoxMatrix.ext {σ τ : CoxMatrix m} (ha : σ.a = τ.a) (hb : σ.b = τ.b) (hd : σ.d = τ.d) : σ = τ`
(one `cases`-proof) and use it everywhere; `toFin` then serves only the `Fintype`/`DecidableEq`
instances. Difficulty: trivial, real payoff.

**`transformedJSeries_coeff` — candidate `@[simp]`** — it is a `rfl`-lemma unfolding the
coefficient; every use site rewrites with it manually. Tagging `@[simp]` (or at least `@[simp]` on
the `ofSuppBddBelow` reformulation) shortens `transformedJSeries_map`,
`transformed_leading`, `cox_a_le`. Difficulty: trivial.

**`jIntCoeff_spec` — candidate `@[simp]`** (rewrites `(laurentqExpansion 1 j).coeff n` to the
integer cast; used five times, always via explicit `rw`). Check for simp-loop with
`laurentqExpansion` lemmas first. Difficulty: trivial.

**`IsGamma0ModularFunction` closure lemmas** — `.mul` and `.polynomialIn` exist; `add`/`sub`/
`const_smul` closure exists only as the ad-hoc private
`isGamma0ModularFunction_sub_const_mul_pow`. If the predicate is kept, a small `add`/`neg`/`const`
kit (or a `Subring` of modular functions) would replace it. Difficulty: easy.

---

## Verified no-change (leads checked and REFUTED or confirmed optimal)

**`BivariatePolynomial` (REFUTED lead)** — `Polynomial (Polynomial R)` **is** mathlib's own
bivariate convention: `Mathlib/Algebra/Polynomial/Bivariate.lean` defines the `R[X][Y]`/`Y`
notations (the project opens `scoped Polynomial.Bivariate`) and even provides
`Polynomial.equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R` should MvPolynomial ever be
needed. Switching to `MvPolynomial (Fin 2) R` would move *away* from the richer API. The project
correctly reuses `evalEval`, `Polynomial.Bivariate.swap`, `swap_monomial`, `swap_swap_apply`,
`aevalAeval_swap`, `coe_aevalAeval_eq_evalEval`, `map_evalRingHom_eval`,
`map_mapRingHom_eval_map`, `eval₂_evalRingHom`. Genuinely missing from mathlib (upstream
candidates, both proved here by `induction_on'`): `BivariatePolynomial.coeff_coeff_swap`
(`(swap Φ).coeff i |>.coeff j = (Φ.coeff j).coeff i` — no `coeff`×`swap` lemma exists in the
mathlib file) and `BivariatePolynomial.map_swap` (naturality of `swap` in the coefficient ring).
`specializeY`/`diagonal` have no mathlib counterparts; their support lemmas correctly bottom out in
mathlib's Bivariate lemmas.

**`sigmaZero` (REFUTED lead)** — `Cox.sigmaZero m` is the distinguished Cox matrix `diag(m,1)`,
not a divisor-counting function; `ArithmeticFunction.sigma 0` (= number of divisors) is unrelated
both in meaning and in value (`|C(m)| = m·∏(1+1/p)`, the Dedekind ψ, not σ₀). Only actionable note:
the name collides mentally with σ₀; `CoxMatrix.distinguished` or `sigma0Matrix` would read better —
cosmetic only.

**`coxDivisorSum*` Euler product (Cardinality.lean)** — mathlib has **no Dedekind psi**
(repo-wide grep for `dedekindPsi`/"Dedekind psi": zero hits), so the divisor-sum/multiplicativity/
prime-power pipeline cannot be replaced. The file already uses the correct mathlib API:
`ArithmeticFunction` + `IsMultiplicative.multiplicative_factorization`,
`Nat.sum_divisors_prime_pow`, `Nat.sum_totient`, `Nat.totient_mul`, `Nat.totient_prime_pow`,
`Nat.filter_coprime_Ico_eq_totient`, `Nat.Coprime.divisors_mul`,
`Nat.prod_factorization_pow_eq_self`. The whole `coxDivisorSumAux = Dedekind ψ` package (value at
prime powers, multiplicativity, Euler product) is a first-class `mathlibable` candidate. An
alternative derivation via Dirichlet convolution `ψ = id ∗ μ²` with
`ArithmeticFunction.IsMultiplicative.mul` was considered and rejected: the termwise identity costs
as much as the current direct proof.

**`Gamma0RightCosets` / `coxMatrixEquivRightCosets`** — uses the correct and only available
mathlib coset API (`QuotientGroup.rightRel`, `rightRel_apply`, `Quotient.map'/liftOn`,
`quotientRightRelEquivQuotientLeftRel`, `Subgroup.fintypeQuotientOfFiniteIndex`,
`CongruenceSubgroup.instFiniteIndexGamma0`, `CongruenceSubgroup.Gamma0_mem`,
`ModularGroup.bottom_row_coprime`, `IsCoprime.exists_SL2_col`
(`LinearAlgebra/Matrix/SpecialLinearGroup.lean:429`),
`Matrix.SpecialLinearGroup.SL2_inv_expl`). `Mathlib.NumberTheory.Modular` (fundamental domain) is
already used elsewhere (`ModularGroup.fd`, `exists_smul_mem_fd` in ModularFunction.lean). No
mathlib equivalence `CoxMatrix m ≃ right cosets` exists; the HNF classification is the intended
project content.

**`zeta`/`zetaField` (partially REFUTED lead)** — `Complex.isPrimitiveRoot_exp`,
`IsPrimitiveRoot.autToPow`, `autToPow_spec`, `ZMod.val_coe_unit_coprime`,
`IsCyclotomicExtension.{finiteDimensional,isGalois}`, `IsGalois.mem_range_algebraMap_iff_fixed`
(`FieldTheory/Galois/Basic.lean:342`), `IsIntegrallyClosed.algebraMap_eq_of_integral` — all the
right API, model usage. Mathlib **does** have
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`
(`NumberTheory/Cyclotomic/Basic.lean:491`) matching `zetaField_isCyclotomicExtension`, **but** it
requires `[Algebra.IsIntegral K L]` — false for `ℚ ⊆ ℂ` — so the project's instance (which only
uses integrality of ζ itself, via `adjoin_simple_toSubalgebra_of_isAlgebraic` +
`IsPrimitiveRoot.adjoin_isCyclotomicExtension`) is a strict generalization: not replaceable;
upstream-the-generalization candidate. Switching to the abstract `CyclotomicField m ℚ` was
considered and rejected: the descent needs a concrete subfield of ℂ, and an embedding would have
to be chosen anyway. `Polynomial.cyclotomic` is not needed anywhere here.

**`holomorphicFunctions`/`HolomorphicFunction`/`FunctionField`
(UpperHalfPlaneFunctionField.lean)** — mathlib's manifold algebra
(`Geometry/Manifold/Algebra/SmoothFunctions.lean`) provides ring instances only on the bundled
`ContMDiffMap` type, not a `Subring (ℍ → ℂ)` of `MDifferentiable` functions; a subring of the Pi
ring is required here so that `Pi.evalRingHom`, `FractionRing`, and `IsFractionRing` compose — the
current design is right. `MDiff` is mathlib's own scoped notation
(`Analysis/Complex/UpperHalfPlane/Manifold.lean`). `ratFuncEvalJ` uses exactly the intended API:
`RatFunc.liftRingHom`, `RatFunc.liftRingHom_injective`,
`nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`, `IsFractionRing.ringEquivOfRingEquiv`,
`IsFractionRing.injective`, `RatFunc.induction_on`. No change.

**`eval_interpolation_sum_at` (Interpolation.lean)** — no mathlib counterpart:
`Lagrange.interpolate` is the *normalized* (division-by-weights) form, deliberately avoided here
because the recovery formula divides once at the end. Could be cosmetically restated via
`Lagrange.nodal`/`eval_nodal_at_node` but the `Finset.sum_eq_single` core remains. Keep.

**`interpolationAt` vs `Lagrange.interpolate`** — same verdict: Cox's unnormalized interpolation
sum is intentional (weights absorbed into the `Φ'` denominator); replacing it with
`Lagrange.interpolate` would force field divisions inside every coefficient-modularity proof. Keep.

**`Represents` / `levelJElement` / `gamma0ModularFunctionField` (ModularFunctionField.lean)** —
`IntermediateField.adjoin` + `adjoin_le_iff` + `subset_adjoin` + membership lemmas is the correct
mathlib pattern; `Represents` (pointwise-a.e. equality of a meromorphic function with a fraction)
is genuinely analytic glue with no mathlib analogue; `represents_unique` cannot be replaced by
`IsFractionRing.mk'` reasoning because its content is the identity-theorem cross-multiplication.
No change.

**`IsGamma0ModularFunction`'s cusp treatment, `SlashInvariantFormClass.periodic_comp_ofComplex`,
`ModularForm.SL_slash_apply`, `ModularFormClass.levelOne_weight_zero_const`,
`OnePoint.isBoundedAt_iff_exists_SL2Z`, `isCusp_SL2Z_iff'`** (ModularFunction.lean) — heavy,
correct reuse of mathlib's modular-forms and cusp API; the weight-0 `ModularForm` packaging in
`levelOne_constant_of_holomorphic` is exactly how mathlib wants Liouville-type arguments phrased.
No change.

**IntegralDescent's descent chain** — `Polynomial.lifts` (`Algebra/Polynomial/Lifts.lean`),
`HahnSeries.C`, `HahnSeries.order_pow`, `HahnSeries.leadingCoeff_*` all correct; no mathlib
`LaurentSeries`-with-ℤ-coefficients type exists (checked `RingTheory/LaurentSeries.lean` — only
`ofPowerSeries`, `powerSeriesPart` etc.), so the subring approach stands (modulo the dedup noted
above).

---

## Summary of refuted leads
1. `BivariatePolynomial` vs `MvPolynomial (Fin 2)` — refuted; `R[X][Y]` *is* the mathlib idiom.
2. `sigmaZero` vs `ArithmeticFunction.sigma 0` — refuted; unrelated objects.
3. `coxDivisorSum*` vs richer `ArithmeticFunction` API — refuted; mathlib lacks Dedekind ψ, and
   everything replaceable is already replaced.
4. `zetaField` instance vs `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` —
   refuted as replacement (mathlib hypothesis `Algebra.IsIntegral ℚ ℂ` fails); project version is
   more general.
5. `matrixStar` vs `Matrix.adjugate` — partially refuted: not equal to adjugate (sign pattern
   differs); equals a `submatrix`/`transpose` conjugate — optional refactor only.
6. `Gamma0RightCosets` machinery vs mathlib coset/modular API — refuted; already optimal.
7. Meromorphic modular-function class in mathlib — confirmed absent; predicate must stay.
