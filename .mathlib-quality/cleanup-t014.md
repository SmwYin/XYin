# Cleanup record: T014

## Baseline and scope

- Targets: `coxMatrixEquivRightCosets`, `rightCosetTranslate`, `rightCosetEval`,
  `rightCosetEval_equiv`, and `rightCosetTranslate_sigmaZero` in
  `XYin/PhD/Cox/CoxMatrices.lean`.
- The implementation proves Cox Lemma 11.11 by a canonical column-HNF reduction and then
  defines both analytic operations as genuine quotient lifts.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- For `γ : SL₂(ℤ)`, `coxInput m γ` is the column-oriented matrix
  `!![γ₁₁,mγ₀₁;γ₁₀,mγ₀₀]`.  It has determinant `m` and content one.
- Right multiplication by `SL₂(ℤ)` preserves content.  Existence and uniqueness of column HNF
  therefore give a canonical `coxRepresentative m γ : CoxMatrix m`.
- The exact kernel calculation is
  `rightRel Γ₀(m) γ δ ↔ coxRepresentative m γ = coxRepresentative m δ`.
  The direction agrees with mathlib's convention `rightRel H γ δ ↔ δγ⁻¹ ∈ H`.
- Surjectivity uses a primitive rank-two Smith normalization.  A finite-prime-factor
  avoidance argument chooses `x` with `Coprime a (b+x*d)`; two explicit determinant-one
  basis changes then prove `L⁻¹ * σ.inclusionMatrix * R = diag(1,m)`.
- The quotient-to-HNF map is bijective, and its inverse is the public
  `coxMatrixEquivRightCosets`.
- `rightCosetTranslate` lifts `γ ↦ f (γ • τ)`.  Its well-definedness is exactly
  weight-zero `Γ₀(m)` invariance, with no representative choice exposed in the API.
- Applying the star involution to the HNF reduction gives
  `δ⁻¹ diag(m,1) γ = σ.mobiusMatrix`.  Modular invariance of `j` and the resulting
  Möbius calculation prove `rightCosetEval_equiv` with the correct action direction.
- `sigmaZero` reduces the identity matrix, hence corresponds to the identity right coset.

## Cleanup and simplify

- Removed unused determinant, star-inverse, star-multiplication, and obsolete Möbius-uniqueness
  helpers after the final proof route was fixed.
- Kept the generic content/HNF/Smith machinery private; the public surface consists of the
  equivalence, quotient operations, their representative simp lemmas, and Cox's two equations.
- Added `rightCosetTranslate_mk` and `rightCosetEval_mk` as the useful quotient computation API.
- All new lines are at most 100 characters and `git diff --check` passes.

## Validation

- `/tmp/T014Validation.lean` checks the identity right coset at level one, `sigmaZero`, both
  equivalence inverse laws, and the translate/evaluation directions.
- `/tmp/T014Axioms.lean` independently checks the same interfaces and audits all five targets.
  Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; none contains
  `sorryAx`.
- The structural `C(1)`, `C(2)`, and `C(3)` enumerations from T013 transfer across the new
  equivalence to the corresponding right-coset types.
- Independent reviews reproduced the exact-kernel proof, Smith normalization, quotient-lift
  orientation, analytic matrix calculation, and identity-coset specialization.
- Focused and 3872-job repository builds pass.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled `rightCosetEval_equiv` validation emits no
  slow-declaration entry; all public targets are below the 1000 ms budget.
- No heartbeat override, profiler scaffold, native-decision axiom, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level import audit
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
