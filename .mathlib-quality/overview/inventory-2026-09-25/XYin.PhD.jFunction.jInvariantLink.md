# Inventory: XYin/PhD/jFunction/jInvariantLink.lean  (81 lines)

Attaches the short Weierstrass model `Y² = X³ − (g₂/4)X − (g₃/4)` to a mathlib `PeriodPair` and proves that mathlib's algebraic `WeierstrassCurve.j` equals the project's lattice invariant `PeriodPair.j` (Cox/LatticeJ.lean:59) and, for the normalized lattice `[1, τ]`, the analytic `j τ`. Leaf file: nothing imports it except `XYin.lean`.

## Declarations

### `def PeriodPair.weierstrassCurve`
- **Type**: `(L : PeriodPair) : WeierstrassCurve ℂ` (:= `⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩`)
- **What**: The short Weierstrass curve whose classical form is y² = 4x³ − g₂x − g₃ (after y ↦ 2y).
- **How**: definition via the structure constructor.
- **Hypotheses**: none
- **Uses from project**: [] (mathlib `PeriodPair`, `PeriodPair.g₂`, `PeriodPair.g₃`: `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60,951,954`)
- **Used by**: instance IsShortNF, weierstrassCurve_c₄, weierstrassCurve_c₆, weierstrassCurve_Δ, instance IsElliptic, weierstrassCurve_j, UpperHalfPlane.ellipticCurve
- **Visibility**: public
- **Lines**: 33–34
- **Notes**: no mathlib bridge lattice → WeierstrassCurve (grep `WeierstrassCurve|discriminant|UpperHalfPlane` in `Elliptic/Weierstrass.lean`: none; `PeriodPair` in `AlgebraicGeometry/EllipticCurve/`: none). 0 external uses.

### `instance PeriodPair.weierstrassCurve.IsShortNF`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.IsShortNF`
- **What**: a₁ = a₂ = a₃ = 0 for the lattice model.
- **How**: `⟨rfl, rfl, rfl⟩` (mathlib class `WeierstrassCurve.IsShortNF`, `AlgebraicGeometry/EllipticCurve/NormalForms.lean:185`).
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve]
- **Used by**: weierstrassCurve_c₄, weierstrassCurve_c₆, weierstrassCurve_Δ, weierstrassCurve_j (through the `*_of_isShortNF` lemmas)
- **Visibility**: public (anonymous)
- **Lines**: 36
- **Notes**: —

### `theorem PeriodPair.weierstrassCurve_c₄`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.c₄ = 12 * L.g₂`
- **What**: c₄ of the lattice model is 12g₂.
- **How**: mathlib `WeierstrassCurve.c₄_of_isShortNF` (NormalForms.lean:213: `c₄ = -48 a₄`), `ring`.
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve]
- **Used by**: weierstrassCurve_j
- **Visibility**: public
- **Lines**: 39–42
- **Notes**: —

### `theorem PeriodPair.weierstrassCurve_c₆`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.c₆ = 216 * L.g₃`
- **What**: c₆ of the lattice model is 216g₃.
- **How**: mathlib `c₆_of_isShortNF` (NormalForms.lean:216), `ring`.
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 45–48
- **Notes**: 0 uses project-wide; documentation-grade.

### `theorem PeriodPair.weierstrassCurve_Δ`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.Δ = L.discriminant`
- **What**: The Weierstrass discriminant equals the lattice discriminant g₂³ − 27g₃² (normalizations agree).
- **How**: mathlib `Δ_of_isShortNF` (NormalForms.lean:219: `Δ = -16(4a₄³ + 27a₆²)`), unfold project `PeriodPair.discriminant`, `ring`.
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve, PeriodPair.discriminant (Cox/LatticeJ.lean:56)]
- **Used by**: instance IsElliptic, weierstrassCurve_j
- **Visibility**: public
- **Lines**: 51–54
- **Notes**: —

### `instance PeriodPair.weierstrassCurve.IsElliptic`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.IsElliptic`
- **What**: The lattice model is an elliptic curve (Δ ≠ 0).
- **How**: `weierstrassCurve_Δ ▸ L.discriminant_ne_zero.isUnit` (mathlib class `WeierstrassCurve.IsElliptic`, `Weierstrass.lean:363`).
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve, weierstrassCurve_Δ, PeriodPair.discriminant_ne_zero (LatticeJ.lean:279)]
- **Used by**: weierstrassCurve_j, instance UpperHalfPlane.ellipticCurve.IsElliptic
- **Visibility**: public (anonymous)
- **Lines**: 56–57
- **Notes**: —

### `theorem PeriodPair.weierstrassCurve_j` `@[simp]`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.j = L.j`
- **What**: Mathlib's j-invariant of the lattice model is Cox's `1728 g₂³/(g₂³ − 27g₃²)`.
- **How**: unfold mathlib `WeierstrassCurve.j` (= `Δ'⁻¹ * c₄³`, `Weierstrass.lean:385`), `Units.val_inv_eq_inv_val`, `coe_Δ'`, then the c₄ and Δ lemmas and project `PeriodPair.j`; `ring`.
- **Hypotheses**: none
- **Uses from project**: [weierstrassCurve, weierstrassCurve_c₄, weierstrassCurve_Δ, PeriodPair.j (LatticeJ.lean:59)]
- **Used by**: UpperHalfPlane.ellipticCurve_j
- **Visibility**: public
- **Lines**: 60–64
- **Notes**: mathlib `WeierstrassCurve.j_of_isShortNF` (`NormalForms.lean:247`: `j = 6912 a₄³/(4a₄³+27a₆²)`, needs `[IsElliptic] [IsShortNF]` over a field) gives this in one `rw` + `field_simp`/`ring`, making `_c₄` and `_Δ` unnecessary for the proof.

### `def UpperHalfPlane.ellipticCurve`
- **Type**: `(τ : ℍ) : WeierstrassCurve ℂ` (:= `(periodPair τ).weierstrassCurve`)
- **What**: The elliptic curve of the lattice ℤ + ℤτ.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [UpperHalfPlane.periodPair (LatticeJ.lean:154), PeriodPair.weierstrassCurve]
- **Used by**: instance, ellipticCurve_j
- **Visibility**: public
- **Lines**: 71
- **Notes**: no clash with mathlib (no `EllipticCurve` structure exists in the pinned mathlib; grep `structure EllipticCurve`: none).

### `instance UpperHalfPlane.ellipticCurve.IsElliptic`
- **Type**: `(τ : ℍ) : (ellipticCurve τ).IsElliptic`
- **What**: Non-degeneracy of the normalized model.
- **How**: `inferInstanceAs` from the PeriodPair instance.
- **Hypotheses**: none
- **Uses from project**: [ellipticCurve, periodPair, instance PeriodPair.weierstrassCurve.IsElliptic]
- **Used by**: ellipticCurve_j (to state `.j`)
- **Visibility**: public (anonymous)
- **Lines**: 73–74
- **Notes**: needed because `ellipticCurve` is a `def`, not `abbrev`.

### `theorem UpperHalfPlane.ellipticCurve_j` `@[simp]`
- **Type**: `(τ : ℍ) : (ellipticCurve τ).j = _root_.j τ`
- **What**: Mathlib's algebraic j of the curve of ℤ+ℤτ is the analytic modular j(τ).
- **How**: `weierstrassCurve_j` composed with project `j_eq_periodPair_j` (LatticeJ.lean:221).
- **Hypotheses**: none
- **Uses from project**: [ellipticCurve, periodPair, PeriodPair.weierstrassCurve_j, j_eq_periodPair_j (LatticeJ.lean:221), j (jfunction.lean:51)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 77–79
- **Notes**: headline result; 0 external uses.

## File Summary
- Total declarations: 10 (2 defs, 5 theorems, 3 instances)
- Key API (used by 3+ others in the file): PeriodPair.weierstrassCurve (7)
- Unused declarations (not used by anything in this file): weierstrassCurve_c₆, ellipticCurve_j (both 0 uses project-wide)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `weierstrassCurve_j` (60–64): use `WeierstrassCurve.j_of_isShortNF` (`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:247`); then `weierstrassCurve_c₄`/`_Δ` are only needed as standalone facts.
- Emphasis (c) answer: mathlib **does** have `PeriodPair`, `lattice`, `G n`, `g₂`, `g₃`, `weierstrassP` (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60–954`) but **no** `PeriodPair.discriminant`, `PeriodPair.j`, and no map `PeriodPair → WeierstrassCurve`; `WeierstrassCurve.j`, `IsElliptic`, `Δ'`, `IsShortNF` and the `*_of_isShortNF` lemmas exist. So the bridge is genuinely project-provided; only its proof can be shortened. The project's `PeriodPair.discriminant`/`.j` (LatticeJ.lean:56,59) are natural upstream candidates to sit next to `g₂`/`g₃`.
### Missing API / repeated patterns
- No `weierstrassCurve_a₄`/`_a₆` simp lemmas (the `change` steps at 41, 47, 53 unfold them manually).
- No statement `(ellipticCurve τ).c₄ = 12 * (periodPair τ).g₂` / relation to `E4 τ` (LatticeJ has `periodPair_g₂_eq_E4`); the file stops at j.
### Junk candidates
- `weierstrassCurve_c₆` (45–48): unused; documentation-grade.
- Whole file is a leaf (only `XYin.lean` imports it) — keep as showcase or move next to LatticeJ.
### Moral duplicates within this batch
- none within the batch; `PeriodPair.j` (LatticeJ.lean:59) vs `WeierstrassCurve.j` are now provably equal here.
### Generalization notes
- `weierstrassCurve`, `_c₄`, `_c₆`, `_Δ` only use ring arithmetic in ℂ; they hold for any `PeriodPair`-like data `(g₂ g₃ : R)` over a `CommRing R` with `4` invertible — a general `WeierstrassCurve.ofShort (a₄ a₆ : R)` with `IsShortNF` instance and `j_of_isShortNF` would subsume them.
