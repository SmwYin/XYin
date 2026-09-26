# Inventory: XYin/PhD/Modularforms/NormNumI.lean  (205 lines)

A **tactic/metaprogram file**, not a lemma file: a vendored copy of the sphere-packing project's `norm_numI` (header: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan, 2025; described in arXiv 2604.23468 "Progress in Formalizing Sphere Packing in Dimension 8"). It parses a closed complex-number expression into `⟨a, b⟩` with `a b : ℝ`, runs `norm_num` on the parts, and exposes (i) a `conv` tactic `norm_numI`, (ii) a debugging `conv` tactic `norm_numI_parse`, and (iii) three `@[norm_num]` extensions for `(z : ℂ) = w`, `Complex.re z`, `Complex.im z`. Everything is declared inside mathlib's own namespaces `Mathlib.Meta.NormNumI` / `Mathlib.Meta.NormNum`. Not present in the pinned mathlib (no `NormNumI`, `norm_numI`, `evalComplexEq` anywhere under `Mathlib/`; `Mathlib/Tactic/NormNum/` has no `Complex` extension). Imported only by Delta.lean (L10); the `norm_numI` conv tactic is invoked nowhere in the project.

## Declarations

### `theorem Mathlib.Meta.NormNumI.split_I`
- **Type**: `I = ⟨0, 1⟩`
- **What**: `I` as a `Complex.mk`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 18
- **Notes**: mathlib has `Complex.I_re`/`I_im`; the `mk` form is what the parser needs.

### `theorem Mathlib.Meta.NormNumI.split_zero`
- **Type**: `(0 : ℂ) = ⟨0, 0⟩`
- **What**: `0` as a `mk`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 20

### `theorem Mathlib.Meta.NormNumI.split_one`
- **Type**: `(1 : ℂ) = ⟨1, 0⟩`
- **What**: `1` as a `mk`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 22

### `theorem Mathlib.Meta.NormNumI.split_add`
- **Type**: `{z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : z₁ = ⟨a₁, b₁⟩) (h₂ : z₂ = ⟨a₂, b₂⟩) : z₁ + z₂ = ⟨a₁ + a₂, b₁ + b₂⟩`
- **What**: Componentwise addition.
- **How**: `substs; rfl`.
- **Hypotheses**: the two decompositions.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 24–28

### `theorem Mathlib.Meta.NormNumI.split_mul`
- **Type**: `… : z₁ * z₂ = ⟨a₁ * a₂ - b₁ * b₂, a₁ * b₂ + b₁ * a₂⟩`
- **What**: Componentwise multiplication.
- **How**: `Complex.ext` with `mul_re`, `mul_im`.
- **Hypotheses**: the two decompositions.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 30–33

### `theorem Mathlib.Meta.NormNumI.split_inv`
- **Type**: `{z : ℂ} {x y : ℝ} (h : z = ⟨x, y⟩) : z⁻¹ = ⟨x / (x * x + y * y), - y / (x * x + y * y)⟩`
- **What**: Componentwise inverse.
- **How**: `Complex.inv_def`, `Complex.ext` with `normSq_apply`, `neg_div`; ends in `rfl` after `simp`.
- **Hypotheses**: decomposition of `z`.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 35–39
- **Notes**: `simp …; rfl` — non-terminal simp closed by `rfl`.

### `theorem Mathlib.Meta.NormNumI.split_neg`
- **Type**: `{z : ℂ} {a b : ℝ} (h : z = ⟨a, b⟩) : -z = ⟨-a, -b⟩`
- **What**: Componentwise negation.
- **How**: `subst; rfl`.
- **Hypotheses**: decomposition.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 41–44

### `theorem Mathlib.Meta.NormNumI.split_conj`
- **Type**: `{w : ℂ} {a b : ℝ} (hw : w = ⟨a, b⟩) : conj w = ⟨a, -b⟩`
- **What**: Componentwise conjugation.
- **How**: `rw [hw]; rfl`.
- **Hypotheses**: decomposition.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 46–49

### `theorem Mathlib.Meta.NormNumI.split_num`
- **Type**: `(n : ℕ) [n.AtLeastTwo] : OfNat.ofNat (α := ℂ) n = ⟨OfNat.ofNat n, 0⟩`
- **What**: Numeric literals `≥ 2` as `mk`.
- **How**: `rfl`.
- **Hypotheses**: `n ≥ 2`.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 51–52

### `theorem Mathlib.Meta.NormNumI.split_scientific`
- **Type**: `(m exp : ℕ) (x : Bool) : (OfScientific.ofScientific m x exp : ℂ) = ⟨(OfScientific.ofScientific m x exp : ℝ), 0⟩`
- **What**: Decimal literals as `mk`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: parse
- **Visibility**: public
- **Lines**: 54–56

### `theorem Mathlib.Meta.NormNumI.eq_eq`
- **Type**: `{z : ℂ} {a b a' b' : ℝ} (pf : z = ⟨a, b⟩) (pf_a : a = a') (pf_b : b = b') : z = ⟨a', b'⟩`
- **What**: Transport a decomposition along normalisations of its parts.
- **How**: `simp_all`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: normalize
- **Visibility**: public
- **Lines**: 58–60

### `theorem Mathlib.Meta.NormNumI.eq_of_eq_of_eq_of_eq`
- **Type**: `{z w : ℂ} {az bz aw bw : ℝ} (hz : z = ⟨az, bz⟩) (hw : w = ⟨aw, bw⟩) (ha : az = aw) (hb : bz = bw) : z = w`
- **What**: Two complex numbers with equal parts are equal.
- **How**: `simp [hz, hw, ha, hb]`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: evalComplexEq
- **Visibility**: public
- **Lines**: 62–64
- **Notes**: mathlib `Complex.ext`/`Complex.ext_iff`.

### `theorem Mathlib.Meta.NormNumI.ne_of_re_ne`
- **Type**: `… (ha : az ≠ aw) : z ≠ w`
- **What**: Different real parts ⇒ different numbers.
- **How**: `simp [hz, hw, ha]`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: evalComplexEq
- **Visibility**: public
- **Lines**: 66–68

### `theorem Mathlib.Meta.NormNumI.ne_of_im_ne`
- **Type**: `… (hb : bz ≠ bw) : z ≠ w`
- **What**: Different imaginary parts ⇒ different numbers.
- **How**: `simp [hz, hw, hb]`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: evalComplexEq
- **Visibility**: public
- **Lines**: 70–72

### `theorem Mathlib.Meta.NormNumI.re_eq_of_eq`
- **Type**: `{z : ℂ} {a b : ℝ} (hz : z = ⟨a, b⟩) : Complex.re z = a`
- **What**: Read off the real part from a decomposition.
- **How**: `simp [hz]`.
- **Hypotheses**: decomposition.
- **Uses from project**: []
- **Used by**: evalRe
- **Visibility**: public
- **Lines**: 74

### `theorem Mathlib.Meta.NormNumI.im_eq_of_eq`
- **Type**: `… : Complex.im z = b`
- **What**: Read off the imaginary part.
- **How**: `simp [hz]`.
- **Hypotheses**: decomposition.
- **Uses from project**: []
- **Used by**: evalIm
- **Visibility**: public
- **Lines**: 75

### `meta partial def Mathlib.Meta.NormNumI.parse`
- **Type**: `(z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩))`
- **What**: Recursively decomposes a closed complex expression built from `+ * ⁻¹ / - conj ^(ℕ literal) I` and numerals into real/imaginary parts with a proof.
- **How**: Qq pattern-matching (`~q(…)`) on the head symbol, recursing and assembling proofs with the `split_*` lemmas; `z₁/z₂ ↦ z₁ * z₂⁻¹`, `z₁ - z₂ ↦ z₁ + -z₂`, `w^(n+1) ↦ w^n * w` (so `w^0` uses `pow_zero`); numerals via `rawNatLit?`, `Nat.AtLeastTwo` synthesis; throws on any other atom.
- **Hypotheses**: n/a (meta).
- **Uses from project**: split_I, split_zero, split_one, split_add, split_mul, split_inv, split_neg, split_conj, split_num, split_scientific
- **Used by**: normalize, norm_numI_parse, evalComplexEq, evalRe, evalIm
- **Visibility**: public (meta)
- **Lines**: 77–130, body ≈ 53 lines
- **Notes**: `partial`; commented-out `Complex.mk` case (L127–129); `n^k` unrolled linearly (exponential blowup in term size for large `k`); does not handle `Complex.ofReal`, `↑(n : ℕ)`/`↑(z : ℤ)` casts, `Real.sqrt`, `π`, or variables — any such atom raises "found the atom … which is not a numeral".

### `meta def Mathlib.Meta.NormNumI.normalize`
- **Type**: `(z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q($z = ⟨$a, $b⟩))`
- **What**: `parse` followed by `norm_num` normalisation of both real parts.
- **How**: `Mathlib.Meta.NormNum.derive` on `a` and `b`, `toSimpResult`, glued by `eq_eq`.
- **Hypotheses**: n/a.
- **Uses from project**: parse, eq_eq
- **Used by**: norm_numI
- **Visibility**: public (meta)
- **Lines**: 132–138
- **Notes**: `| unreachable!` on a `proof?`-less simp result (a `rfl`-result from `derive` would hit this).

### `elab "norm_numI" : conv`
- **Type**: `conv` tactic
- **What**: Rewrites the focused complex expression to `Complex.mk a b` with normalised `a b`.
- **How**: `Conv.getLhs`, type check `ℂ`, `normalize`, `Conv.applySimpResult`.
- **Hypotheses**: n/a.
- **Uses from project**: normalize
- **Used by**: unused in file
- **Visibility**: public (global syntax)
- **Lines**: 140–145
- **Notes**: **never invoked anywhere in XYin** (`grep -rw norm_numI` → only this file).

### `elab "norm_numI_parse" : conv`
- **Type**: `conv` tactic
- **What**: Debug variant that applies `parse` without normalising.
- **How**: as above with `parse`.
- **Hypotheses**: n/a.
- **Uses from project**: parse
- **Used by**: unused in file
- **Visibility**: public (global syntax)
- **Lines**: 147–153
- **Notes**: comment "Testing the `parse` function"; test-only code shipped in the library.

### `@[norm_num (_ : ℂ) = _] meta def Mathlib.Meta.NormNum.evalComplexEq`
- **Type**: `NormNumExt`
- **What**: `norm_num` extension deciding `z = w` for closed complex numerals.
- **How**: `whnfR`, `isDefEq` against `Eq (α := ℂ)`, `parse` both sides, `deriveBool` on the real-part equation then the imaginary-part equation; returns `isBool true` via `eq_of_eq_of_eq_of_eq` or `isBool false` via `ne_of_re_ne`/`ne_of_im_ne`.
- **Hypotheses**: n/a.
- **Uses from project**: parse, eq_of_eq_of_eq_of_eq, ne_of_re_ne, ne_of_im_ne
- **Used by**: unused in file (fires automatically inside any `norm_num` call in importing files)
- **Visibility**: public (registered extension)
- **Lines**: 158–177, body ≈ 16 lines
- **Notes**: docstring. Registered globally on import: any `norm_num`/`simp` with `norm_num` extensions in Delta.lean or Eisensteinqexpansions.lean (which imports Delta) may silently depend on it.

### `@[norm_num Complex.re _] meta def Mathlib.Meta.NormNum.evalRe`
- **Type**: `NormNumExt`
- **What**: `norm_num` extension evaluating `Complex.re z` for closed `z`.
- **How**: matches the `.proj ``Complex 0` structure projection, `parse`, `derive` on the real part, `eqTrans` with `re_eq_of_eq`.
- **Hypotheses**: n/a.
- **Uses from project**: parse, re_eq_of_eq
- **Used by**: unused in file
- **Visibility**: public (registered extension)
- **Lines**: 179–189
- **Notes**: docstring; matches on raw `Expr.proj`, so `Complex.re z` in application form (`.app (.const ``Complex.re) z`) after `whnfR` must reduce to the projection — works for the structure projection but is brittle.

### `@[norm_num Complex.im _] meta def Mathlib.Meta.NormNum.evalIm`
- **Type**: `NormNumExt`
- **What**: Same for `Complex.im`.
- **How**: as `evalRe` with projection index 1 and `im_eq_of_eq`.
- **Hypotheses**: n/a.
- **Uses from project**: parse, im_eq_of_eq
- **Used by**: unused in file
- **Visibility**: public (registered extension)
- **Lines**: 191–201
- **Notes**: docstring.

## File Summary
- Total declarations: 23 (0 ordinary defs; 16 theorems; 0 instances; 7 other: 2 meta defs `parse`/`normalize`, 2 `elab` conv tactics, 3 `@[norm_num]` extensions)
- Key API (used by 3+ others in the file): parse (5)
- Unused declarations (not used by anything in this file): norm_numI, norm_numI_parse, evalComplexEq, evalRe, evalIm (all are entry points; the extensions fire implicitly)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (`parse` is a 53-line meta definition, not a proof)

## Observations

### Mathlib API candidates
- **Not in the pinned mathlib**: `grep -rln "NormNumI\|norm_numI\|evalComplexEq" Mathlib/` is empty, `ls Mathlib/Tactic/NormNum/` contains no `Complex*.lean`, and `Mathlib/Tactic/` has no `NormNumI`. So this is (as of rev 2abc242) a vendored external tactic, not a duplicate — but it is declared into `Mathlib.Meta.NormNum`/`Mathlib.Meta.NormNumI`, so if/when upstream lands the same names, the project will get duplicate-declaration errors on the next bump.
- **What stock mathlib already covers**: for closed numerals the goals these extensions target (`z = w`, `z.re = a`, `z.im = b`) are handled by `simp [Complex.ext_iff]`/`norm_num [Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.inv_re, …]` (all in `Mathlib/Data/Complex/Basic.lean`), i.e. `Complex.ext_iff` + the `re`/`im` simp set + `norm_num` on ℝ. The extension automates the same computation and gives `≠` verdicts; it is a convenience, not new capability.
- **Whether it is load-bearing cannot be determined statically**: Delta.lean (the only importer) contains no `norm_num` call at all (grep: only `positivity`, `simp`, `simpa`, `field_simp`), and the `norm_numI` conv tactic is never used. `positivity`/`field_simp` do call `NormNum.derive` on subterms, so the `Complex.re/im` extensions *could* fire inside Delta.lean's `simp`/`positivity` calls (e.g. Delta.lean:294–331 region has `re`/`im` reasoning). The definitive test is to remove `import XYin.PhD.Modularforms.NormNumI` from Delta.lean:10 and rebuild Delta + Eisensteinqexpansions.
- Lemmas `split_*`, `eq_of_eq_of_eq_of_eq`, `re_eq_of_eq`, `im_eq_of_eq` are all `Complex.ext`/`Complex.ext_iff`-level facts (`Mathlib/Data/Complex/Basic.lean`), kept in `mk`-form deliberately for the parser; no action needed.

### Missing API / repeated patterns
- `evalRe` (L182–189) and `evalIm` (L194–201) are the same 8 lines with projection index 0/1 — a shared helper `evalProj (idx : ℕ) (lemma : Name)` would collapse them.
- `parse` has no case for `Complex.ofReal`/`↑(r : ℝ)` or `Nat`/`Int` casts, which are the atoms that actually appear in the project's complex arithmetic (`(n : ℂ)`, `(π : ℂ)`); as written it can only succeed on literal-only expressions.

### Junk candidates
- `norm_numI_parse` (L147–153): explicitly a test harness ("Testing the `parse` function"); should not ship.
- Commented-out code L127–129.
- `norm_numI` conv tactic (L140–145): never used in the project.
- If the import-removal test passes, the entire file is dead (Delta.lean:10 is its only importer besides `XYin.lean`).

### Moral duplicates within this batch
- `eq_of_eq_of_eq_of_eq` (L62) is `Complex.ext` after `subst`; `ne_of_re_ne`/`ne_of_im_ne` (L66/L70) are `mt (congrArg Complex.re/im)`.
- `evalRe`/`evalIm` (L182/L194).

### Generalization notes
- The `split_*` lemmas and `parse` are specific to `ℂ = ℝ × ℝ` with `Complex.mk`; nothing generalises (by design).
- The extension `evalComplexEq` matches `Eq (α := ℂ)` only; a `norm_num` extension keyed on `(_ : ℂ) ≠ _` is not provided although `ne_of_re_ne`/`ne_of_im_ne` exist (the `isBool false` path already covers `=` goals that are false, which `norm_num` turns into `≠`).
