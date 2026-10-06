# Canonical DVR-place algebra equivalence

Retained `AINTLIBDrafts.DVRPlaceAlgEquiv` reuses the existing native `IsDiscreteValuationRing.equivValuationSubring` as its unchanged ring equivalence. Its new `k`-algebra commutation field is the original scalar-tower identity. The target retains the intrinsic place's actual constant-field algebra; no scalar structure is transported.

Public APIs in `FunctionField.Place`:

- `ofDiscreteValuationRingAlgEquiv k A K` is the canonical `A ≃ₐ[k] (ofDiscreteValuationRing k A K).toValuationSubring`.
- `ofDiscreteValuationRingAlgEquiv_coe` identifies its value in `K` with `algebraMap A K a` by definitional equality.
- `ofDiscreteValuationRingAlgEquiv_symm_coe` identifies the literal embedding of its inverse with the original subtype value, by the equivalence's inverse law.

The assumptions remain exactly the existing DVR/fraction-field constructor's genuine `k → A → K` algebras and scalar tower. No geometric lift, centre identification, scheme injectivity, or place bijection is introduced. Two API examples check a genuine constant coefficient in `K` and recovery of `a` from the literal image subtype.

Temporary source was independently reviewed by the parent before retention: final 56-line probe, session **86374 CLOSED exit 0**, seven permitted prints (six standard-three and `IsScalarTower.algebraMap_apply` with `propext, Quot.sound`), two examples, no diagnostics. The first failed source and complete log were archived; its repairs only specified native implicit `A,K` arguments and the actual tower identity in the coefficient example.

Named source is **70 lines**, maximum width **90**; only license and scope documentation were added. Its complete expose-section suffix equals the accepted probe byte-for-byte, and the retained/work copies are byte-equal. Strict setup has the correct module name, both implicit flags false, and no plugins/dynlibs. Named owner session **44110 CLOSED exit 0** was explicitly polled, with the same full seven prints and two examples, no diagnostics or `sorryAx`.

Full named log: `/private/tmp/DVRPlaceAlgEquiv-named.log`. Exact source/setup/log SHA-256 values and every six canonical artifact plus C output hash/size are saved in `/private/tmp/DVRPlaceAlgEquiv-receipt.json`. The original failed attempt is excluded from this receipt's successful proof checks. Source and named artifacts are frozen; no later geometry claim is included.
