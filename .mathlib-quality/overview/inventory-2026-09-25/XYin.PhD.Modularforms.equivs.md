# Inventory: XYin/PhD/Modularforms/equivs.lean  (46 lines)

Three hand-rolled bijections: negation on ℤ, successor on ℤ, and coordinate swap on `Fin 2 → α` (with two helper lemmas). Imported only by `Summability/Basic.lean` (uses `negEquiv.tsum_eq` and `negEquiv.summable_iff`, L28/L32); `succEquiv`, `swap`, `swap_apply`, `swap_involutive`, `swap_equiv` are unused anywhere (the `swap` hits in `Cox/*.lean` are unrelated identifiers such as `modularPolynomial_map_complex_zero_swap`). Each bijection already exists in mathlib as an `Equiv`.

## Declarations

### `def negEquiv`
- **Type**: `ℤ ≃ ℤ`
- **What**: `n ↦ -n` as a self-inverse bijection of ℤ.
- **How**: `toFun := fun n => -n`, `invFun` likewise, inverse laws by `neg_neg`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally Summability/Basic.lean:28, :32
- **Visibility**: public
- **Lines**: 18–22
- **Notes**: **= mathlib `Equiv.neg ℤ`** (`Mathlib/Algebra/Group/Equiv/Basic.lean:242`, `Equiv.inv` with `@[to_additive (attr := simps! …)]`), which comes with the simp lemma `Equiv.neg_apply`. BigO.lean:52 already uses `(Equiv.neg ℤ)` — the project uses both spellings.

### `def succEquiv`
- **Type**: `ℤ ≃ ℤ`
- **What**: `n ↦ n + 1` (`Int.succ`) with inverse `Int.pred`.
- **How**: `Int.pred_succ`, `Int.succ_pred`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 25–29
- **Notes**: unused anywhere. = mathlib `Equiv.addRight (1 : ℤ)` (`Mathlib/Algebra/Group/Units/Equiv.lean:120`, `Equiv.mulRight` with `@[to_additive]`; `Int.succ n` is by definition `n + 1`).

### `def swap`
- **Type**: `{α : Type*} : (Fin 2 → α) → (Fin 2 → α)`
- **What**: Swaps the two coordinates: `![x 0, x 1] ↦ ![x 1, x 0]`.
- **How**: `fun x => ![x 1, x 0]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: swap_apply, swap_involutive, swap_equiv
- **Visibility**: public
- **Lines**: 35
- **Notes**: unused outside file. Root-namespace `swap` collides with `Function.swap` under `open Function` (which this very file does at L13–14, and most project files do) — overload resolution by type is the only thing keeping it unambiguous. Mathlib: `f ∘ Fin.revPerm` / `Equiv.arrowCongr Fin.revPerm (Equiv.refl α)` (`Mathlib/Data/Fin/Rev.lean:35`, `Mathlib/Logic/Equiv/Defs.lean:451`), or `(finTwoArrowEquiv α).symm ∘ Prod.swap ∘ finTwoArrowEquiv α` (`Mathlib/Logic/Equiv/Fin/Basic.lean:52`).

### `@[simp] lemma swap_apply`
- **Type**: `{α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0]`
- **What**: Unfolding lemma for `swap`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: swap
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 37–38
- **Notes**: unused anywhere; `@[simp]`.

### `lemma swap_involutive`
- **Type**: `{α : Type*} (b : Fin 2 → α) : swap (swap b) = b`
- **What**: `swap` is an involution.
- **How**: `ext i; fin_cases i <;> rfl`.
- **Hypotheses**: none.
- **Uses from project**: swap
- **Used by**: swap_equiv
- **Visibility**: public
- **Lines**: 40–42
- **Notes**: mathlib: `Fin.revPerm_symm`/`Fin.rev_rev` (`Data/Fin/Rev.lean`) or `Function.Involutive`.

### `def swap_equiv`
- **Type**: `{α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α)`
- **What**: `swap` as a self-inverse bijection.
- **How**: `Equiv.mk swap swap` with both inverse laws from `swap_involutive` (after `rw [Function.LeftInverse]` / `[Function.RightInverse]`).
- **Hypotheses**: none.
- **Uses from project**: swap, swap_involutive
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 44–46
- **Notes**: unused anywhere. = `Equiv.arrowCongr Fin.revPerm (Equiv.refl α)` — verified this session by scratch typecheck that `(Equiv.arrowCongr Fin.revPerm (Equiv.refl α)) f = ![f 1, f 0]` holds by `ext i; fin_cases i <;> rfl`. Also `Function.Involutive.toPerm swap swap_involutive` would be the one-line construction.

## File Summary
- Total declarations: 6 (4 defs: negEquiv, succEquiv, swap, swap_equiv; 2 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): swap (3)
- Unused declarations (not used by anything in this file): negEquiv (ext. Summability/Basic), succEquiv, swap_apply, swap_equiv
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `negEquiv` (L18) = `Equiv.neg ℤ` (`Mathlib/Algebra/Group/Equiv/Basic.lean:242`, to_additive of `Equiv.inv`); replacing the two uses in `Summability/Basic.lean:28/32` (`(Equiv.neg ℤ).tsum_eq`, `(Equiv.neg ℤ).summable_iff`) deletes the def. Note mathlib also has `tsum_neg`-style lemmas: `Equiv.tsum_eq (Equiv.neg ℤ)` is the standard idiom.
- `succEquiv` (L25) = `Equiv.addRight (1 : ℤ)` (`Mathlib/Algebra/Group/Units/Equiv.lean:120`).
- `swap_equiv` (L44) = `Equiv.arrowCongr Fin.revPerm (Equiv.refl α)` (`Mathlib/Logic/Equiv/Defs.lean:451`, `Mathlib/Data/Fin/Rev.lean:35`) — typechecked; `swap` = `(· ∘ Fin.rev)`; `swap_involutive` = `Fin.rev_rev` under `funext`.
- Hand-rolled pattern: `Equiv.mk f f h h` for an involution is `Function.Involutive.toPerm`.

### Missing API / repeated patterns
- None to add — all three bijections are mathlib `Equiv`s.

### Junk candidates
- `succEquiv` (L25), `swap` (L35), `swap_apply` (L37), `swap_involutive` (L40), `swap_equiv` (L44): unused anywhere.
- `negEquiv` (L18): replace by `Equiv.neg ℤ` and delete; then the whole file and the import in `Summability/Basic.lean` go.
- Stray imports L3–7 (`Algebra.Order.Ring.Star`, `Analysis.Normed.Ring.Lemmas`, `Data.Int.Star`, `NumberTheory.TsumDivisorsAntidiagonal`, `Mathlib.Tactic`) — `import Mathlib.Tactic` in particular is a heavy import for a 46-line file; `open … Complex` etc. (L13–14) unused.
- Naming hazard: root-level `swap` vs `Function.swap` (opened at L13–14).

### Moral duplicates within this batch
- `negEquiv` (equivs.lean:18) vs `(Equiv.neg ℤ)` used directly in BigO.lean:52.
- `swap` / `swap_equiv` vs BigO.lean's `norm_symm` (which is about the same coordinate swap on `Fin 2 → ℤ`).

### Generalization notes
- `negEquiv`, `succEquiv`: hold in any `AddGroup`/`InvolutiveNeg` (`Equiv.neg G`) and any `AddGroup` (`Equiv.addRight a`); ℤ is a special case.
- `swap`: is `precomposition with `Fin.rev`` for any `n` (here `n = 2`), i.e. `Equiv.arrowCongr Fin.revPerm (Equiv.refl α)` for all `Fin n → α`.
