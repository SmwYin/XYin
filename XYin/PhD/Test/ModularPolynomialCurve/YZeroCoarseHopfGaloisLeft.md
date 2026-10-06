# The canonical Galois map as an equivalence over its left factor

The retained module is `AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.lean`, in namespace
`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft`. It imports only pinned
`ModularCurves.ForMathlib.HopfGalois`.

For commutative rings `R0`, `A`, and `B`, their existing `R0`-algebras, an actual
map `ρ : B →ₐ[R0] B ⊗[R0] A`, and `h : IsHopfGalois ρ`, the definition
`galoisEquivOverLeft h` upgrades the upstream equivalence to

```lean
(B ⊗[coinvariants ρ] B) ≃ₐ[B] (B ⊗[R0] A)
```

Both sides use the standard tensor-product algebra structure from their first
`B` factor. The proof changes the scalar ring via `AlgEquiv.ofRingEquiv`.
Compatibility with this left scalar structure is exactly the actual upstream
`canonicalGaloisMap_comp_includeLeft` equation evaluated at an arbitrary `b : B`.
No new hypothesis is added to the existing `IsHopfGalois` input.

`galoisEquivOverLeft_toRingEquiv` proves by `rfl` that the underlying ring
equivalence is the literal upstream `h.galoisEquiv.toRingEquiv`.
`galoisEquivOverLeft_tmul` preserves the positive formula, also by `rfl`:

```lean
galoisEquivOverLeft h (b ⊗ₜ[coinvariants ρ] b') =
  (b ⊗ₜ[R0] 1) * ρ b'
```

Two sanity examples exercise the actual `B`-algebra scalar map and the elementary
tensor formula. This module supplies a scalar-compatible equivalence; finite
module descent, étaleness, and a global quotient conclusion require separate
instantiations and proofs.

The temporary fixture passed on its first strict elaboration: 47 lines,
SHA-256 `815a6824a08ca04bc28dc06f33cab037f332b48d9af9ae93e96f9d28cad8fe6c`,
receipt `/private/tmp/YZeroHopfGaloisLeftProbe.log`, exit 0, and zero
warnings/errors. All six axiom checks use only standard axioms. The three own
declarations and upstream `galoisEquiv` use `propext`, `Classical.choice`, and
`Quot.sound`; the left-inclusion equation uses `propext` and `Quot.sound`, and
`AlgEquiv.ofRingEquiv` uses `Quot.sound`.

The retained file preserves the accepted proof and sanity bodies, with normal
header/module documentation and docstrings. It has 71 lines and SHA-256
`2bd96940fc2fea8688a9317739e0362987b0f478333070a1dc9de2c9762826e6`.
Correct-name strict artifact emission passed with exit 0, the same six clean
axiom outputs, both examples, and zero diagnostics.
Receipt: `/private/tmp/xyin-y0-hopf-galois-left.log`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The setup `/private/tmp/YZeroCoarseHopfGaloisLeft.setup.json` records module name
`AINTLIBDrafts.YZeroCoarseHopfGaloisLeft` with `autoImplicit = false` and
`relaxedAutoImplicit = false`. From `/private/tmp/xyin-y0-aintlib-work`, the exact
command was:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseHopfGaloisLeft.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.c AINTLIBDrafts/YZeroCoarseHopfGaloisLeft.lean > /private/tmp/xyin-y0-hopf-galois-left.log 2>&1
```

Canonical `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`,
and `.c` artifacts were checked present; retained and isolated source copies
were byte-equal after compilation. Previously frozen leaves and the local
XYin toolchain were unchanged.
