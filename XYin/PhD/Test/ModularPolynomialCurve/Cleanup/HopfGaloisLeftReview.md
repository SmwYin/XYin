# HopfGaloisLeft independent review

Review date: 2026-10-04. **Verdict: PASS.** This is a read-only Lean/source review;
only this Markdown report was written, with no additional compiler invocation.

## Frozen source and delta

[YZeroCoarseHopfGaloisLeft.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.lean)
has 71 lines and SHA-256
`2bd96940fc2fea8688a9317739e0362987b0f478333070a1dc9de2c9762826e6`.
The accepted temporary source had 47 lines and SHA-256
`815a6824a08ca04bc28dc06f33cab037f332b48d9af9ae93e96f9d28cad8fe6c`.
The actual retained diff contains only the license, module exposition, and three
docstrings. Definition, proofs, examples, checks, and sole upstream import are
unchanged. Retained and isolated copies were independently checked byte-equal.

## Scalar and ring-map check

For commutative rings `R0`, `A`, `B`, their stated `R0`-algebra structures, the
actual map `ρ : B →ₐ[R0] B ⊗[R0] A`, and `h : IsHopfGalois ρ`, the new definition
has type

```lean
(B ⊗[coinvariants ρ] B) ≃ₐ[B] (B ⊗[R0] A)
```

Both tensor products use the standard algebra structure from their **left**
`B` factor. The underlying ring equivalence is the literal upstream
`h.galoisEquiv.toRingEquiv`. Its new scalar obligation is precisely

```lean
canonicalGaloisMap ρ (b ⊗ₜ[coinvariants ρ] 1) = b ⊗ₜ[R0] 1
```

for arbitrary `b : B`, obtained by evaluating the actual upstream
`canonicalGaloisMap_comp_includeLeft` equality. There is no right-factor
structure or inverse Galois map substituted here.

The pinned upstream `ForMathlib/HopfGalois.lean:73` defines the canonical map
by the left inclusion and the coaction; `:85` proves its left-inclusion formula;
`:113` records `IsHopfGalois`; and `:127` packages the same canonical map using
its actual bijectivity field. The wrapper adds no coaction, Hopf-algebra,
finite-module, or geometric hypothesis to that existing record.

The two preservation theorems are actual `rfl` proofs: the underlying ring
equivalence is unchanged, and the elementary-tensor formula remains

```lean
galoisEquivOverLeft h (b ⊗ₜ[coinvariants ρ] b') =
  (b ⊗ₜ[R0] 1) * ρ b'
```

## Named strict receipt and boundary

Named emission session 81306 closed with exit 0. The actual log
`/private/tmp/xyin-y0-hopf-galois-left.log` has six clean prints: the three own
declarations and upstream `galoisEquiv` use the standard three axioms; the
left-inclusion equation uses `propext` and `Quot.sound`; `AlgEquiv.ofRingEquiv`
uses `Quot.sound`. No warnings/errors occur. The `B`-scalar-map sanity and the
positive tensor-formula sanity both pass.

The actual setup `/private/tmp/YZeroCoarseHopfGaloisLeft.setup.json` names
`AINTLIBDrafts.YZeroCoarseHopfGaloisLeft`, sets both implicit-variable options
to `false`, and contains no plugins or dynamic libraries. Canonical artifacts
were independently checked: `.olean` 66224 bytes, `.olean.private` 11800,
`.olean.server` 3064, `.ilean` 5412, `.ir` 1512, and `.ir.sig` 176.
Pins and the literal invocation are preserved in the paired
[verification report](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/YZeroCoarseHopfGaloisLeft.md).

This module changes the recorded scalar ring of an existing equivalence.
Finite-module descent, quotient-map finiteness, étaleness, quotient properness,
and a quotient Weierstrass model are separate obligations. None is asserted or
assumed by these declarations.
