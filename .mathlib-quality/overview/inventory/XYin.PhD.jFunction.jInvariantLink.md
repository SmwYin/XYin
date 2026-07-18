# XYin/PhD/jFunction/jInvariantLink.lean
Project-internal imports: `XYin.PhD.Cox.LatticeJ`

### `def PeriodPair.weierstrassCurve`
- **Type**: `(L : PeriodPair) → WeierstrassCurve ℂ`
- **What**: Attaches to a complex period lattice `L` the short Weierstrass model `y² = x³ − (g₂/4)x − (g₃/4)`, i.e. the curve with coefficients `a₁ = a₂ = a₃ = 0`, `a₄ = −g₂/4`, `a₆ = −g₃/4`. This is the classical Weierstrass ℘-function uniformization normalized for Mathlib's long Weierstrass form.
- **How**: Direct anonymous-constructor definition; the `/4` normalization compensates for Mathlib's `y² + …` convention so that `c₄ = 12g₂` and `Δ = g₂³ − 27g₃²` come out on the nose.
- **Hypotheses**: `L` is a `PeriodPair` (an ordered ℝ-basis pair of ℂ with positive imaginary ratio, from `LatticeJ`).
- **Uses from project**: [`PeriodPair`, `PeriodPair.g₂`, `PeriodPair.g₃`]
- **Used by**: `IsShortNF` instance, `weierstrassCurve_c₄`, `weierstrassCurve_c₆`, `weierstrassCurve_Δ`, `IsElliptic` instance, `weierstrassCurve_j`, `UpperHalfPlane.ellipticCurve`
- **Visibility**: public
- **Lines**: 32–34, def (1 line)
- **Notes**: none

### `instance [anonymous] : L.weierstrassCurve.IsShortNF`
- **Type**: `(L : PeriodPair) → L.weierstrassCurve.IsShortNF`
- **What**: Records that the lattice model is in short normal form (`a₁ = a₂ = a₃ = 0`), unlocking Mathlib's simplified `c₄`/`c₆`/`Δ` formulas for short Weierstrass curves.
- **How**: The three coefficient equations hold by `rfl` since the curve is defined with literal zeros.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: [`PeriodPair.weierstrassCurve`]
- **Used by**: `weierstrassCurve_c₄`, `weierstrassCurve_c₆`, `weierstrassCurve_Δ` (each rewrites with an `_of_isShortNF` lemma requiring this instance)
- **Visibility**: public (anonymous instance)
- **Lines**: 36, proof 1 line
- **Notes**: none

### `theorem PeriodPair.weierstrassCurve_c₄`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.c₄ = 12 * L.g₂`
- **What**: The fourth Weierstrass invariant of the lattice model equals `12 g₂`, matching the classical normalization `c₄ = 12 g₂(L)`.
- **How**: Rewrites with Mathlib's `WeierstrassCurve.c₄_of_isShortNF` (valid by the `IsShortNF` instance), reducing to the algebraic identity `−48 · (−g₂/4) = 12 g₂`, closed by `ring`.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: [`PeriodPair.weierstrassCurve`, `PeriodPair.g₂`]
- **Used by**: `weierstrassCurve_j`
- **Visibility**: public
- **Lines**: 38–42, proof 3 lines
- **Notes**: none

### `theorem PeriodPair.weierstrassCurve_c₆`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.c₆ = 216 * L.g₃`
- **What**: The sixth Weierstrass invariant of the lattice model equals `216 g₃`, the classical normalization `c₆ = 216 g₃(L)`.
- **How**: Rewrites with Mathlib's `WeierstrassCurve.c₆_of_isShortNF`, reducing to `−864 · (−g₃/4) = 216 g₃`, closed by `ring`.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: [`PeriodPair.weierstrassCurve`, `PeriodPair.g₃`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 44–48, proof 3 lines
- **Notes**: none

### `theorem PeriodPair.weierstrassCurve_Δ`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.Δ = L.discriminant`
- **What**: The Weierstrass discriminant of the lattice model equals the project's lattice discriminant `g₂³ − 27 g₃²` exactly (same normalization, no factor of 16 discrepancy).
- **How**: Rewrites with Mathlib's `WeierstrassCurve.Δ_of_isShortNF` and unfolds `PeriodPair.discriminant`, reducing to `−16(4(−g₂/4)³ + 27(−g₃/4)²) = g₂³ − 27g₃²`, closed by `ring`.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: [`PeriodPair.weierstrassCurve`, `PeriodPair.discriminant`, `PeriodPair.g₂`, `PeriodPair.g₃`]
- **Used by**: `IsElliptic` instance, `weierstrassCurve_j`
- **Visibility**: public
- **Lines**: 50–56, proof 5 lines
- **Notes**: none

### `instance [anonymous] : L.weierstrassCurve.IsElliptic`
- **Type**: `(L : PeriodPair) → L.weierstrassCurve.IsElliptic`
- **What**: The lattice model is an elliptic curve, i.e. its discriminant is a unit in ℂ. This is the analytic fact that a genuine period lattice has nonvanishing discriminant.
- **How**: Reduces via `WeierstrassCurve.isElliptic_iff` and `weierstrassCurve_Δ` to the project theorem `PeriodPair.discriminant_ne_zero` (nonvanishing of `g₂³ − 27g₃²` for a lattice), promoted to `IsUnit` in the field ℂ.
- **Hypotheses**: none beyond `L : PeriodPair` (nonvanishing is a theorem, not an assumption).
- **Uses from project**: [`PeriodPair.weierstrassCurve`, `weierstrassCurve_Δ`, `PeriodPair.discriminant_ne_zero`]
- **Used by**: `weierstrassCurve_j` (needed for `WeierstrassCurve.j` and `Δ'` to exist), `UpperHalfPlane` `IsElliptic` instance
- **Visibility**: public (anonymous instance)
- **Lines**: 58–60, proof 2 lines
- **Notes**: none

### `theorem PeriodPair.weierstrassCurve_j`
- **Type**: `(L : PeriodPair) : L.weierstrassCurve.j = L.j`
- **What**: The Mathlib elliptic-curve `j`-invariant (`c₄³/Δ`) of the lattice model coincides with Cox's lattice invariant `j(L) = 1728 g₂³ / (g₂³ − 27g₃²)`. This is the bridge between the algebraic-geometry and lattice-theoretic invariants.
- **How**: Unfolds `WeierstrassCurve.j = Δ'⁻¹ · c₄³` via `Units.val_inv_eq_inv_val` and `WeierstrassCurve.coe_Δ'`, then substitutes `weierstrassCurve_c₄` (`c₄ = 12g₂`, so `c₄³ = 1728 g₂³`) and `weierstrassCurve_Δ`; `ring` closes the resulting field identity.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: [`PeriodPair.weierstrassCurve`, `weierstrassCurve_c₄`, `weierstrassCurve_Δ`, `PeriodPair.j`]
- **Used by**: `UpperHalfPlane.ellipticCurve_j`
- **Visibility**: public
- **Lines**: 62–67, proof 3 lines
- **Notes**: `@[simp]`

### `def UpperHalfPlane.ellipticCurve`
- **Type**: `(τ : ℍ) → WeierstrassCurve ℂ`
- **What**: The short Weierstrass model attached to the normalized period lattice `[1, τ]` for a point `τ` of the upper half-plane.
- **How**: Composes `UpperHalfPlane.periodPair` (the lattice `[1, τ]` from `LatticeJ`) with `PeriodPair.weierstrassCurve`.
- **Hypotheses**: `τ ∈ ℍ`.
- **Uses from project**: [`UpperHalfPlane.periodPair`, `PeriodPair.weierstrassCurve`]
- **Used by**: `IsElliptic` instance for `ellipticCurve τ`, `ellipticCurve_j`
- **Visibility**: public
- **Lines**: 73–74, def (1 line)
- **Notes**: none

### `instance [anonymous] : (ellipticCurve τ).IsElliptic`
- **Type**: `(τ : ℍ) → (UpperHalfPlane.ellipticCurve τ).IsElliptic`
- **What**: The normalized-lattice model is an elliptic curve (nonzero discriminant).
- **How**: Unfolds `ellipticCurve` to `(periodPair τ).weierstrassCurve` and invokes the `PeriodPair`-level `IsElliptic` instance by `infer_instance`.
- **Hypotheses**: `τ ∈ ℍ`.
- **Uses from project**: [`UpperHalfPlane.ellipticCurve`, `UpperHalfPlane.periodPair`, `PeriodPair.weierstrassCurve`, the `PeriodPair` `IsElliptic` instance]
- **Used by**: `ellipticCurve_j` (implicitly, for `WeierstrassCurve.j` to be defined)
- **Visibility**: public (anonymous instance)
- **Lines**: 76–78, proof 2 lines
- **Notes**: none

### `theorem UpperHalfPlane.ellipticCurve_j`
- **Type**: `(τ : ℍ) : (ellipticCurve τ).j = _root_.j τ`
- **What**: The Mathlib `j`-invariant of the elliptic curve attached to the lattice `[1, τ]` equals the analytic modular function `j(τ) = E₄(τ)³/Δ(τ)`. This completes the three-way identification analytic `j` = lattice `j` = curve `j`.
- **How**: Chains `PeriodPair.weierstrassCurve_j` (curve invariant = lattice invariant) with the `LatticeJ` theorem `j_eq_periodPair_j` (analytic `j(τ)` = lattice invariant of `[1, τ]`, i.e. Eisenstein-series computation of `g₂, g₃`).
- **Hypotheses**: `τ ∈ ℍ`.
- **Uses from project**: [`UpperHalfPlane.ellipticCurve`, `PeriodPair.weierstrassCurve_j`, `j_eq_periodPair_j`, `j` (analytic, from `XYin.PhD.jFunction.jfunction` via `LatticeJ`)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 80–83, proof 1 line
- **Notes**: `@[simp]`

### File Summary
- Total declarations: 10 (2 defs, 5 lemmas/theorems, 3 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`PeriodPair.weierstrassCurve` (used by 7)]
- Unused declarations (not used by anything in this file): [`weierstrassCurve_c₆`, `ellipticCurve_j`]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
