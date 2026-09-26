# Inventory: XYin/PhD/ModularFunctions/MeromorphicField.lean  (658 lines)

A port (header lines 1–26, copyright Stefan Kebekus) of five ProjectVD `VD/Field` files concatenated into one module: (i) eventual statements along `Filter.codiscreteWithin U` versus punctured neighbourhoods of points of `U`; (ii) `NeBot` criteria for `codiscreteWithin`; (iii) vanishing of meromorphic germs; (iv) the ring `MeromorphicOn.germRing 𝕜 U` — the image of the subring of meromorphic functions in `Filter.Germ (codiscreteWithin U) 𝕜` — with a pointwise `Inv` and a `Field` instance under `Fact (IsPreconnected U)`/`Fact U.Nontrivial`; (v) supporting API (`constRingHom`/`Algebra 𝕜`, `orderAt`, `divisor`, normal-form representative `toNF`). The final section specialises to `UpperHalfPlane.MeromorphicField := germRing ℂ upperHalfPlaneSet` with a canonical representative `toFun : MeromorphicField → ℍ → ℂ` and constructors `ofMeromorphic`/`ofHolomorphic`; this is the ambient field for `ModularFunction` (Basic.lean) and the Cox function-field files.

## Declarations

### `theorem Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE`
- **Type**: `(h : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y) : ∀ᶠ y in codiscreteWithin U, p y`
- **What**: A predicate that holds eventually on every punctured neighbourhood of every point of `U` holds eventually along `codiscreteWithin U` (any set `U`, any topological space).
- **How**: Unfolds membership via mathlib's `mem_codiscreteWithin_iff_forall_mem_nhdsNE` and enlarges `{p} ` to `{p} ∪ Uᶜ` by `mem_of_superset`/`subset_union_left`.
- **Hypotheses**: pointwise eventual truth on `𝓝[≠] x` for all `x ∈ U`.
- **Uses from project**: []
- **Used by**: `Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE`, `Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`
- **Visibility**: public
- **Lines**: 46–49, proof body ≈ 2 lines
- **Notes**: Not in pinned mathlib (searched name and `eventually_codiscreteWithin`). Used cross-file by FieldAction.lean:83.

### `theorem Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE`
- **Type**: `(h : ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g) : f =ᶠ[codiscreteWithin U] g`
- **What**: Two functions agreeing on punctured neighbourhoods of all points of `U` agree along `codiscreteWithin U`.
- **How**: Instance of the previous lemma with `p y := f y = g y`.
- **Hypotheses**: local agreement near each point of `U`.
- **Uses from project**: `Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE`
- **Used by**: `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top`
- **Visibility**: public
- **Lines**: 55–57, proof body ≈ 1 line
- **Notes**: one-line specialisation; not in mathlib.

### `theorem Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`
- **Type**: `(hU : IsOpen U) : (∀ᶠ y in codiscreteWithin U, p y) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y`
- **What**: For open `U` the converse also holds: eventual truth along `codiscreteWithin U` is equivalent to eventual truth on every punctured neighbourhood inside `U`.
- **How**: Backward direction is the first lemma; forward direction takes `mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx`, intersects with `U ∈ 𝓝[≠] x` (`mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)`) and discharges the `Uᶜ` alternative with `Or.resolve_right`.
- **Hypotheses**: `U` open.
- **Uses from project**: `Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE`
- **Used by**: `eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE`
- **Visibility**: public
- **Lines**: 63–68, proof body ≈ 4 lines
- **Notes**: Not in mathlib. Used cross-file by FieldAction.lean:85.

### `lemma eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE`
- **Type**: `(hU : IsOpen U) : f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g`
- **What**: On an open set, agreement along `codiscreteWithin U` is the same as agreement on the punctured neighbourhood of every point of `U`.
- **How**: Instance of the previous iff with `p y := f y = g y`.
- **Hypotheses**: `U` open.
- **Uses from project**: `Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`
- **Used by**: `MeromorphicOn.GermRing.eqOn_toNF_of_meromorphicNFOn`
- **Visibility**: public
- **Lines**: 75–77, proof body ≈ 1 line
- **Notes**: Declared in the ROOT namespace while its three siblings are `Filter.*` (inconsistent; `lemma` vs `theorem` too). Docstring (line 73) cites `eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE`, which exists neither in the project nor in mathlib — stale ProjectVD cross-reference.

### `theorem Filter.codiscreteWithin_neBot_iff`
- **Type**: `(codiscreteWithin S).NeBot ↔ ¬IsDiscrete S`
- **What**: `codiscreteWithin S` is a nontrivial filter exactly when `S` is not a discrete set.
- **How**: `neBot_iff` plus mathlib's `codiscreteWithin_eq_bot_iff`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 97–98, proof body ≈ 1 line
- **Notes**: One-line rewrap of `Mathlib/Topology/DiscreteSubset.lean:369 codiscreteWithin_eq_bot_iff`; unused anywhere in the project.

### `theorem AccPt.codiscreteWithin_neBot`
- **Type**: `(hx : x ∈ S) (h : AccPt x (𝓟 S)) : (codiscreteWithin S).NeBot`
- **What**: If some point of `S` is an accumulation point of `S`, the codiscrete filter is nontrivial.
- **How**: `accPt_principal_iff_nhdsWithin` turns the hypothesis into `(𝓝[S \ {x}] x).NeBot`; `codiscreteWithin S` is the `iSup` of these, so `neBot_of_le (le_iSup₂ …)`.
- **Hypotheses**: `x ∈ S`, `x` accumulation point of `S`.
- **Uses from project**: []
- **Used by**: `Preperfect.codiscreteWithin_neBot`
- **Visibility**: public
- **Lines**: 102–105, proof body ≈ 2 lines
- **Notes**: relies on the definitional unfolding of `codiscreteWithin` as an `iSup` (fragile if mathlib changes the definition).

### `theorem Preperfect.codiscreteWithin_neBot`
- **Type**: `(hS : Preperfect S) (hne : S.Nonempty) : (codiscreteWithin S).NeBot`
- **What**: Nonempty preperfect sets have nontrivial codiscrete filter.
- **How**: pick `x ∈ S`; preperfectness gives `AccPt x (𝓟 S)`; apply `AccPt.codiscreteWithin_neBot`.
- **Hypotheses**: `S` preperfect and nonempty.
- **Uses from project**: `AccPt.codiscreteWithin_neBot`
- **Used by**: `IsPreconnected.codiscreteWithin_neBot`
- **Visibility**: public
- **Lines**: 108–111, proof body ≈ 2 lines
- **Notes**: —

### `theorem IsPreconnected.codiscreteWithin_neBot`
- **Type**: `[T1Space X] (hS : IsPreconnected S) (h2S : S.Nontrivial) : (codiscreteWithin S).NeBot`
- **What**: A preconnected set with at least two points has nontrivial codiscrete filter.
- **How**: mathlib `IsPreconnected.preperfect_of_nontrivial` then `Preperfect.codiscreteWithin_neBot`.
- **Hypotheses**: T1 space, `S` preconnected with ≥ 2 points.
- **Uses from project**: `Preperfect.codiscreteWithin_neBot`
- **Used by**: `instance … Nontrivial (germRing 𝕜 U)` (line 309), `MeromorphicOn.GermRing.isField`
- **Visibility**: public
- **Lines**: 115–117, proof body ≈ 1 line
- **Notes**: —

### `theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top`
- **Type**: `(hf : MeromorphicOn f U) (hU : Preperfect U) : f =ᶠ[codiscreteWithin U] 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤`
- **What**: On a preperfect set a meromorphic function vanishes codiscretely iff it has infinite order at every point.
- **How**: (→) mathlib `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin` + `meromorphicOrderAt_eq_top_iff`; (←) `Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE` + `meromorphicOrderAt_eq_top_iff`.
- **Hypotheses**: `f` meromorphic on `U`, `U` preperfect; `f : 𝕜 → E` (vector-valued).
- **Uses from project**: `Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE`
- **Used by**: `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top`, `MeromorphicOn.GermRing.coe_eq_zero_iff`
- **Visibility**: public
- **Lines**: 143–152, proof body ≈ 8 lines
- **Notes**: —

### `theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top`
- **Type**: `(hf : MeromorphicOn f U) (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : f =ᶠ[codiscreteWithin U] 0 ↔ ∃ x ∈ U, meromorphicOrderAt f x = ⊤`
- **What**: Identity theorem in codiscrete form: on a preconnected set with ≥ 2 points a meromorphic function vanishes codiscretely iff it has infinite order at one point.
- **How**: reduce to the `∀` version via `preperfect_of_nontrivial`; the `∃ → ∀` step is mathlib's `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall` (contrapositive, `by_contra`).
- **Hypotheses**: `f` meromorphic on `U`; `U` preconnected, nontrivial.
- **Uses from project**: `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top`
- **Used by**: `MeromorphicOn.GermRing.mul_inv_cancel`
- **Visibility**: public
- **Lines**: 158–170, proof body ≈ 11 lines
- **Notes**: —

### `theorem MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin`
- **Type**: `(hs : MeromorphicOn s U) (h : ∀ x ∈ U, meromorphicOrderAt s x ≠ ⊤) : s * s⁻¹ =ᶠ[codiscreteWithin U] 1`
- **What**: A meromorphic function of finite order everywhere is codiscretely invertible by its pointwise inverse.
- **How**: mathlib `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero` gives `{s ≠ 0} ∈ codiscreteWithin U`; `mul_inv_cancel₀` pointwise.
- **Hypotheses**: `s : 𝕜 → 𝕜'` meromorphic on `U`, finite order at all points of `U`.
- **Uses from project**: []
- **Used by**: `MeromorphicOn.GermRing.mul_inv_cancel`
- **Visibility**: public
- **Lines**: 176–180, proof body ≈ 2 lines
- **Notes**: calls the mathlib lemma by its odd full name `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero` (declared inside `namespace MeromorphicAt` in `Mathlib/Analysis/Meromorphic/IsolatedZeros.lean:71`).

### `def MeromorphicOn.subring`
- **Type**: `(𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : Subring (𝕜 → 𝕜)`
- **What**: Functions meromorphic on `U` as a subring of all functions `𝕜 → 𝕜`.
- **How**: carrier `{f | MeromorphicOn f U}`, closure by `MeromorphicOn.const/add/mul/neg`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `mem_subring_iff`, `germRing`, `toGermRingHom`
- **Visibility**: public
- **Lines**: 211–217
- **Notes**: no mathlib analogue (searched `Subring|Subalgebra` in `Mathlib/Analysis/Meromorphic/`). Could be a `Subalgebra 𝕜 (𝕜 → 𝕜)` (constants are meromorphic).

### `theorem MeromorphicOn.mem_subring_iff`
- **Type**: `f ∈ subring 𝕜 U ↔ MeromorphicOn f U`
- **What**: membership unfolds to meromorphy.
- **How**: `Iff.rfl`.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicOn.subring`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 219–220
- **Notes**: `@[simp]`; unused in the project.

### `def MeromorphicOn.germRing`
- **Type**: `(𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : Subring (Germ (codiscreteWithin U) 𝕜)`
- **What**: The ring of germs (along `codiscreteWithin U`) of meromorphic functions, as the image of `subring 𝕜 U` under the germ map.
- **How**: `(subring 𝕜 U).map (Germ.coeRingHom _)`.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicOn.subring`
- **Used by**: every later declaration in the file.
- **Visibility**: public
- **Lines**: 231–233
- **Notes**: This is the mathlib-idiomatic construction (`Filter.Germ` + `Subring.map` + `Germ.coeRingHom`, `Mathlib/Order/Filter/Germ/Basic.lean:600`), not a hand-rolled `Setoid`. Mathlib's `Filter.Germ.instField` (`Mathlib/Order/Filter/FilterProduct.lean:65`) is only for ultrafilters, so the ambient germ ring is NOT a field; restricting to meromorphic germs is exactly what is needed.

### `theorem MeromorphicOn.mem_germRing_iff`
- **Type**: `{γ : Germ (codiscreteWithin U) 𝕜} : γ ∈ germRing 𝕜 U ↔ ∃ f, MeromorphicOn f U ∧ (f : Germ _ 𝕜) = γ`
- **What**: A germ is in `germRing` iff it has a meromorphic representative.
- **How**: both directions are `Subring.mem_map` unpacking (anonymous constructor shuffling).
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicOn.germRing`
- **Used by**: `coe_mem_germRing`, `toGermRingHom_surjective`, `instance Inv`, `GermRing.mul_inv_cancel`, `GermRing.out`
- **Visibility**: public
- **Lines**: 236–238
- **Notes**: is literally `Subring.mem_map` / `Set.mem_image`; used cross-file by FieldAction.lean:104,121.

### `theorem MeromorphicOn.coe_mem_germRing`
- **Type**: `(hf : MeromorphicOn f U) : (f : Germ (codiscreteWithin U) 𝕜) ∈ germRing 𝕜 U`
- **What**: the germ of a meromorphic function lies in `germRing`.
- **How**: `mem_germRing_iff.2 ⟨f, hf, rfl⟩`.
- **Hypotheses**: `f` meromorphic on `U`.
- **Uses from project**: `mem_germRing_iff`
- **Used by**: `toGermRingHom`, `GermRing.constRingHom`
- **Visibility**: public
- **Lines**: 241–243
- **Notes**: —

### `def MeromorphicOn.toGermRingHom`
- **Type**: `subring 𝕜 U →+* germRing 𝕜 U`
- **What**: the quotient ring homomorphism from meromorphic functions to meromorphic germs.
- **How**: `(Germ.coeRingHom _).comp (subring 𝕜 U).subtype` cod-restricted by `coe_mem_germRing`.
- **Hypotheses**: none.
- **Uses from project**: `subring`, `germRing`, `coe_mem_germRing`
- **Used by**: `toGermRingHom_surjective`, `GermRing.toGermRingHom_toNF`, `MeromorphicField.ofMeromorphic`
- **Visibility**: public
- **Lines**: 246–248
- **Notes**: —

### `theorem MeromorphicOn.toGermRingHom_surjective`
- **Type**: `Function.Surjective (toGermRingHom (𝕜 := 𝕜) (U := U))`
- **What**: every meromorphic germ comes from a meromorphic function.
- **How**: unpack `mem_germRing_iff`.
- **Hypotheses**: none.
- **Uses from project**: `toGermRingHom`, `mem_germRing_iff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 250–254, proof body ≈ 3 lines
- **Notes**: unused in project; is `Subring.map`'s `RingHom.rangeRestrict_surjective` in disguise.

### `instance MeromorphicOn.GermRing.instInv` (anonymous `noncomputable instance : Inv (germRing 𝕜 U)`)
- **Type**: `Inv (germRing 𝕜 U)`
- **What**: pointwise inverse of germs (junk value `0⁻¹ = 0`) stays inside `germRing` because `f⁻¹` is meromorphic when `f` is.
- **How**: `MeromorphicOn.inv` on a chosen representative plus `Germ.coe_inv`.
- **Hypotheses**: none on `U`.
- **Uses from project**: `germRing`, `mem_germRing_iff`
- **Used by**: `coe_inv`, `instance Div`, `inv_zero`, `mul_inv_cancel`, `instField`, `divisor_inv`
- **Visibility**: public
- **Lines**: 266–269
- **Notes**: auto-generated instance name; mathlib style would name it `instInv`.

### `theorem MeromorphicOn.GermRing.coe_inv`
- **Type**: `(a : germRing 𝕜 U) : ((a⁻¹ : germRing 𝕜 U) : Germ _ 𝕜) = (a : Germ _ 𝕜)⁻¹`
- **What**: coercion commutes with inverse.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `instance Inv`
- **Used by**: `inv_zero`, `divisor_inv`
- **Visibility**: public
- **Lines**: 271–274
- **Notes**: `@[simp, norm_cast]`.

### `instance MeromorphicOn.GermRing.instDiv` (anonymous `noncomputable instance : Div (germRing 𝕜 U)`)
- **Type**: `Div (germRing 𝕜 U)`
- **What**: division defined as `a * b⁻¹`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `instance Inv`
- **Used by**: `div_eq_mul_inv`, `coe_div`, `instField`
- **Visibility**: public
- **Lines**: 276–277
- **Notes**: auto-generated name.

### `theorem MeromorphicOn.GermRing.div_eq_mul_inv`
- **Type**: `(a b : germRing 𝕜 U) : a / b = a * b⁻¹`
- **What**: unfolding of division.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `instance Div`
- **Used by**: `coe_div`
- **Visibility**: public
- **Lines**: 279
- **Notes**: shadows the global `div_eq_mul_inv` inside the namespace; redundant once `instField` is available.

### `theorem MeromorphicOn.GermRing.coe_div`
- **Type**: `(a b : germRing 𝕜 U) : ((a / b : germRing 𝕜 U) : Germ _ 𝕜) = (a : Germ _ 𝕜) / (b : Germ _ 𝕜)`
- **What**: coercion commutes with division.
- **How**: rewrite both sides with `div_eq_mul_inv`/`division_def`, `push_cast`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `div_eq_mul_inv`, `instance Div`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281–287, proof body ≈ 3 lines
- **Notes**: `@[simp, norm_cast]`; unused in project.

### `theorem MeromorphicOn.GermRing.inv_zero` (protected)
- **Type**: `(0 : germRing 𝕜 U)⁻¹ = 0`
- **What**: the junk convention holds for germs.
- **How**: `Subtype.ext`, `coe_inv`, rewrite `0` as `↑(0 : 𝕜 → 𝕜)`, `Germ.coe_inv`, `Germ.coe_eq`, `filter_upwards`, `simp`.
- **Hypotheses**: none.
- **Uses from project**: `coe_inv`, `instance Inv`
- **Used by**: `instField`
- **Visibility**: protected
- **Lines**: 289–295, proof body ≈ 6 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.nontrivial`
- **Type**: `(h : (codiscreteWithin U).NeBot) : Nontrivial (germRing 𝕜 U)`
- **What**: `0 ≠ 1` in the germ ring whenever the filter is nontrivial.
- **How**: `Germ.coe_eq` + `.exists` on `0 =ᶠ 1` yields a point with `0 = 1` in `𝕜`.
- **Hypotheses**: `codiscreteWithin U` nontrivial.
- **Uses from project**: `germRing`
- **Used by**: `instance Nontrivial`, `isField`
- **Visibility**: public
- **Lines**: 302–307, proof body ≈ 5 lines
- **Notes**: derivable from mathlib instances: `Germ.instNontrivial [NeBot l]` (`Mathlib/Order/Filter/Germ/Basic.lean:528`) + `instance [Nontrivial R] (s : Subring R) : Nontrivial s` (`Mathlib/Algebra/Ring/Subring/Defs.lean:365`), i.e. `haveI := h; inferInstance`.

### `instance MeromorphicOn.GermRing.instNontrivial…` (anonymous, `[Fact (IsPreconnected U)] [Fact U.Nontrivial] : Nontrivial (germRing 𝕜 U)`)
- **Type**: `Nontrivial (germRing 𝕜 U)`
- **What**: the `Fact`-driven instance version of `nontrivial`.
- **How**: `IsPreconnected.codiscreteWithin_neBot`.
- **Hypotheses**: `Fact (IsPreconnected U)`, `Fact U.Nontrivial`.
- **Uses from project**: `nontrivial`, `IsPreconnected.codiscreteWithin_neBot`
- **Used by**: `instField` (`exists_pair_ne _`), `isDomain`
- **Visibility**: public
- **Lines**: 309–311
- **Notes**: auto-generated name `instNontrivialSubtypeGermCodiscreteWithinMemSubringGermRingOfIsPreconnectedOfFactNontrivial` (verified via `#synth`); should be named. A `Fact`-driven `NeBot (codiscreteWithin U)` instance would make this and `nontrivial` redundant.

### `theorem MeromorphicOn.GermRing.coe_eq_zero_iff`
- **Type**: `(hf : MeromorphicOn f U) (hU : Preperfect U) : (f : Germ _ 𝕜) = 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤`
- **What**: the germ of a meromorphic function vanishes iff the function has infinite order everywhere on `U`.
- **How**: `Germ.coe_eq` + `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top`.
- **Hypotheses**: `f` meromorphic on preperfect `U`.
- **Uses from project**: `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top`
- **Used by**: `eq_zero_iff_forall_orderAt_eq_top`
- **Visibility**: public
- **Lines**: 317–320, proof body ≈ 2 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.mul_inv_cancel` (protected)
- **Type**: `(h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a : germRing 𝕜 U} (ha : a ≠ 0) : a * a⁻¹ = 1`
- **What**: nonzero meromorphic germs on a connected set are invertible by the pointwise inverse.
- **How**: representative `f`; `ha` + `eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top` gives finite order everywhere; conclude with `self_mul_inv_eventuallyEq_one_codiscreteWithin` after `push_cast`/`Germ.coe_eq`.
- **Hypotheses**: `U` preconnected with ≥ 2 points; `a ≠ 0`.
- **Uses from project**: `mem_germRing_iff`, `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top`, `MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin`, `instance Inv`
- **Used by**: `isField`, `instField`
- **Visibility**: protected
- **Lines**: 326–343, proof body ≈ 16 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.isField`
- **Type**: `(h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsField (germRing 𝕜 U)`
- **What**: unbundled field property.
- **How**: `nontrivial`, `mul_comm`, `mul_inv_cancel`.
- **Hypotheses**: `U` preconnected, nontrivial.
- **Uses from project**: `nontrivial`, `IsPreconnected.codiscreteWithin_neBot`, `mul_inv_cancel`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 344–347
- **Notes**: unused in project (the `Fact`-instance `instField` is used instead).

### `instance MeromorphicOn.GermRing.instField`
- **Type**: `[Fact (IsPreconnected U)] [Fact U.Nontrivial] : Field (germRing 𝕜 U)`
- **What**: the field of meromorphic germs on a connected set, with the pointwise inverse.
- **How**: extends the `Subring` `CommRing` (`__ := inferInstance`), `inv := Inv.inv`, `div := Div.div`, `mul_inv_cancel` from the protected lemma, `inv_zero`, `nnqsmul/qsmul := _`.
- **Hypotheses**: the two `Fact`s.
- **Uses from project**: `instance Inv`, `instance Div`, `instance Nontrivial`, `mul_inv_cancel`, `inv_zero`
- **Used by**: `isDomain`; all ℍ-level consumers via `MeromorphicField`.
- **Visibility**: public
- **Lines**: 353–363
- **Notes**: `#synth Field MeromorphicField` resolves to this instance; no competing `Field`/`Inv`/`Div` path (scratch-verified). `CommRing` data is shared with `Subring.toCommRing`, so no diamond.

### `theorem MeromorphicOn.GermRing.isDomain`
- **Type**: `(h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsDomain (germRing 𝕜 U)`
- **What**: unbundled domain property.
- **How**: build the two `Fact`s locally and `inferInstance` through `instField`.
- **Hypotheses**: `U` preconnected, nontrivial.
- **Uses from project**: `instField`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 366–369
- **Notes**: unused in project.

### `def MeromorphicOn.GermRing.out`
- **Type**: `(a : germRing 𝕜 U) : 𝕜 → 𝕜`
- **What**: a chosen meromorphic representative of a germ.
- **How**: `(mem_germRing_iff.1 a.2).choose`.
- **Hypotheses**: none.
- **Uses from project**: `mem_germRing_iff`
- **Used by**: `meromorphicOn_out`, `coe_out`, `orderAt`, `divisor`, `toNF`
- **Visibility**: public
- **Lines**: 406
- **Notes**: noncomputable choice; representative is not canonical (that is `toNF`).

### `theorem MeromorphicOn.GermRing.meromorphicOn_out`
- **Type**: `(a : germRing 𝕜 U) : MeromorphicOn (out a) U`
- **What**: the chosen representative is meromorphic.
- **How**: `choose_spec.1`.
- **Hypotheses**: none.
- **Uses from project**: `out`, `mem_germRing_iff`
- **Used by**: `orderAt_coe`, `orderAt_mul`, `eq_zero_iff_forall_orderAt_eq_top`, `orderAt_ne_top`, `divisor_coe`, `divisor_mul`, `divisor_inv`, `meromorphicNFOn_toNF`, `coe_toNF`
- **Visibility**: public
- **Lines**: 409–410
- **Notes**: —

### `theorem MeromorphicOn.GermRing.coe_out`
- **Type**: `(a : germRing 𝕜 U) : ((out a : 𝕜 → 𝕜) : Germ _ 𝕜) = a`
- **What**: the representative represents.
- **How**: `choose_spec.2`.
- **Hypotheses**: none.
- **Uses from project**: `out`, `mem_germRing_iff`
- **Used by**: `out_eventuallyEq`, `orderAt_mul`, `eq_zero_iff_forall_orderAt_eq_top`, `divisor_mul`, `divisor_inv`, `coe_toNF`
- **Visibility**: public
- **Lines**: 412–415
- **Notes**: `@[simp]`.

### `theorem MeromorphicOn.GermRing.out_eventuallyEq`
- **Type**: `{a} (hfa : (f : Germ _ 𝕜) = a) : f =ᶠ[codiscreteWithin U] out a`
- **What**: any representative agrees codiscretely with the chosen one.
- **How**: `Germ.coe_eq.1` after `rw [hfa, coe_out]`.
- **Hypotheses**: `f` represents `a`.
- **Uses from project**: `coe_out`
- **Used by**: `orderAt_coe`, `divisor_coe`
- **Visibility**: public
- **Lines**: 418–420
- **Notes**: —

### `def MeromorphicOn.GermRing.constRingHom`
- **Type**: `(𝕜) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : 𝕜 →+* germRing 𝕜 U`
- **What**: embedding of constants into the germ ring.
- **How**: `(Germ.coeRingHom _).comp (Pi.constRingHom 𝕜 𝕜)` cod-restricted via `coe_mem_germRing (const c)`.
- **Hypotheses**: none.
- **Uses from project**: `germRing`, `coe_mem_germRing`
- **Used by**: `coe_constRingHom`, `constRingHom_injective`, `instance Algebra`, `algebraMap_eq_constRingHom`
- **Visibility**: public
- **Lines**: 427–429
- **Notes**: mathlib has `Pi.constRingHom` (`Mathlib/Algebra/Ring/Pi.lean:167`) and `Filter.Germ.const` (`Germ/Basic.lean:119`) but no `Algebra R (Germ l A)`; see Observations.

### `theorem MeromorphicOn.GermRing.coe_constRingHom`
- **Type**: `(c : 𝕜) : ((constRingHom 𝕜 U c : germRing 𝕜 U) : Germ _ 𝕜) = ((fun _ ↦ c : 𝕜 → 𝕜) : Germ _ 𝕜)`
- **What**: the underlying germ of a constant.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `constRingHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 431–435
- **Notes**: `@[simp]`; RHS could be stated as `Germ.const c`/`(c : Germ _ 𝕜)`; unused in project.

### `theorem MeromorphicOn.GermRing.constRingHom_injective`
- **Type**: `(h : (codiscreteWithin U).NeBot) : Function.Injective (constRingHom 𝕜 U)`
- **What**: distinct constants have distinct germs when the filter is nontrivial.
- **How**: `Germ.coe_eq` + `.exists`.
- **Hypotheses**: `NeBot`.
- **Uses from project**: `constRingHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 438–442, proof body ≈ 3 lines
- **Notes**: unused in project; redundant with `RingHom.injective` once the target is a field.

### `instance MeromorphicOn.GermRing.instAlgebra` (anonymous `noncomputable instance : Algebra 𝕜 (germRing 𝕜 U)`)
- **Type**: `Algebra 𝕜 (germRing 𝕜 U)`
- **What**: the germ ring is a `𝕜`-algebra via constants.
- **How**: `(constRingHom 𝕜 U).toAlgebra`.
- **Hypotheses**: none.
- **Uses from project**: `constRingHom`
- **Used by**: `algebraMap_eq_constRingHom`
- **Visibility**: public
- **Lines**: 445
- **Notes**: scratch-verified: `SMul ℂ MeromorphicField` and `Module ℂ MeromorphicField` resolve only through this instance (`SMulMemClass (Subring (Germ …)) ℂ _` does not synthesize), and `c • a = constRingHom c * a` is `rfl` — no diamond. Auto-generated name.

### `theorem MeromorphicOn.GermRing.algebraMap_eq_constRingHom`
- **Type**: `algebraMap 𝕜 (germRing 𝕜 U) = constRingHom 𝕜 U`
- **What**: unfolding of the algebra map.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `instance Algebra`, `constRingHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 447–448
- **Notes**: unused in project.

### `def MeromorphicOn.GermRing.orderAt`
- **Type**: `(a : germRing 𝕜 U) (x : 𝕜) : WithTop ℤ`
- **What**: order of a germ at a point, via the chosen representative.
- **How**: `meromorphicOrderAt (out a) x`.
- **Hypotheses**: none (well-defined only on preperfect sets, see `orderAt_coe`).
- **Uses from project**: `out`
- **Used by**: `orderAt_coe`, `orderAt_mul`, `eq_zero_iff_forall_orderAt_eq_top`, `orderAt_ne_top`
- **Visibility**: public
- **Lines**: 457–458
- **Notes**: no germ-level order in mathlib; underlying API is `meromorphicOrderAt` (`Mathlib/Analysis/Meromorphic/Order.lean`).

### `theorem MeromorphicOn.GermRing.orderAt_coe`
- **Type**: `(hU : Preperfect U) (hf : MeromorphicOn f U) (hx : x ∈ U) {a} (hfa : (f : Germ _ 𝕜) = a) : orderAt a x = meromorphicOrderAt f x`
- **What**: independence of the representative on preperfect sets.
- **How**: mathlib `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect` upgrades `out_eventuallyEq` to `𝓝[≠] x`, then `meromorphicOrderAt_congr`.
- **Hypotheses**: `U` preperfect, `x ∈ U`, `f` meromorphic representative.
- **Uses from project**: `orderAt`, `meromorphicOn_out`, `out_eventuallyEq`
- **Used by**: `orderAt_mul`
- **Visibility**: public
- **Lines**: 462–468, proof body ≈ 4 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.orderAt_mul`
- **Type**: `(hU : Preperfect U) (hx : x ∈ U) (a b : germRing 𝕜 U) : orderAt (a * b) x = orderAt a x + orderAt b x`
- **What**: additivity of order on products.
- **How**: `orderAt_coe` with representative `out a * out b` (`push_cast [coe_out]`), then mathlib `meromorphicOrderAt_mul`.
- **Hypotheses**: `U` preperfect, `x ∈ U`.
- **Uses from project**: `orderAt_coe`, `meromorphicOn_out`, `coe_out`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 470–474, proof body ≈ 3 lines
- **Notes**: unused in project; companions `orderAt_one/_inv/_add_ge/_algebraMap` missing.

### `theorem MeromorphicOn.GermRing.eq_zero_iff_forall_orderAt_eq_top`
- **Type**: `(hU : Preperfect U) {a} : a = 0 ↔ ∀ x ∈ U, orderAt a x = ⊤`
- **What**: a germ vanishes iff infinite order everywhere.
- **How**: `Subtype.ext_iff`, `← coe_out`, `coe_eq_zero_iff`.
- **Hypotheses**: `U` preperfect.
- **Uses from project**: `coe_out`, `coe_eq_zero_iff`, `meromorphicOn_out`, `orderAt`
- **Used by**: `orderAt_ne_top`
- **Visibility**: public
- **Lines**: 477–480, proof body ≈ 2 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.orderAt_ne_top`
- **Type**: `(h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a} (ha : a ≠ 0) (hx : x ∈ U) : orderAt a x ≠ ⊤`
- **What**: nonzero germs have finite order at every point of a connected set (so `orderAt · x` is a ℤ-valued valuation).
- **How**: negate `eq_zero_iff_forall_orderAt_eq_top` (`push Not`), propagate with mathlib `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`.
- **Hypotheses**: `U` preconnected, nontrivial; `a ≠ 0`; `x ∈ U`.
- **Uses from project**: `eq_zero_iff_forall_orderAt_eq_top`, `meromorphicOn_out`
- **Used by**: `divisor_mul`
- **Visibility**: public
- **Lines**: 485–492, proof body ≈ 6 lines
- **Notes**: docstring promises a valuation, but no `AddValuation`/`Valuation` is constructed.

### `def MeromorphicOn.GermRing.divisor`
- **Type**: `(a : germRing 𝕜 U) : Function.locallyFinsuppWithin U ℤ`
- **What**: divisor of a germ via the chosen representative.
- **How**: `MeromorphicOn.divisor (out a) U`.
- **Hypotheses**: none.
- **Uses from project**: `out`
- **Used by**: `divisor_coe`, `divisor_mul`, `divisor_inv`
- **Visibility**: public
- **Lines**: 501–502
- **Notes**: underlying mathlib API `MeromorphicOn.divisor` (`Mathlib/Analysis/Meromorphic/Divisor.lean`).

### `theorem MeromorphicOn.GermRing.divisor_coe`
- **Type**: `(hU : Preperfect U) (hf : MeromorphicOn f U) {a} (hfa : (f : Germ _ 𝕜) = a) : divisor a = MeromorphicOn.divisor f U`
- **What**: independence of representative.
- **How**: mathlib `divisor_of_eventuallyEq_codiscreteWithin_preperfect` with `out_eventuallyEq`.
- **Hypotheses**: `U` preperfect; `f` meromorphic representative.
- **Uses from project**: `divisor`, `meromorphicOn_out`, `out_eventuallyEq`
- **Used by**: `divisor_mul`, `divisor_inv`
- **Visibility**: public
- **Lines**: 506–511, proof body ≈ 3 lines
- **Notes**: —

### `theorem MeromorphicOn.GermRing.divisor_mul`
- **Type**: `(h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a b} (ha : a ≠ 0) (hb : b ≠ 0) : divisor (a * b) = divisor a + divisor b`
- **What**: divisor is additive on nonzero germs.
- **How**: `divisor_coe` with representative `out a * out b`, mathlib `MeromorphicOn.divisor_mul` with finiteness from `orderAt_ne_top`.
- **Hypotheses**: `U` preconnected, nontrivial; `a, b ≠ 0`.
- **Uses from project**: `divisor_coe`, `meromorphicOn_out`, `coe_out`, `orderAt_ne_top`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 515–523, proof body ≈ 6 lines
- **Notes**: unused in project.

### `theorem MeromorphicOn.GermRing.divisor_inv`
- **Type**: `(hU : Preperfect U) (a : germRing 𝕜 U) : divisor a⁻¹ = -divisor a`
- **What**: divisor of the inverse germ.
- **How**: `divisor_coe` with representative `(out a)⁻¹` (`Germ.coe_inv`, `coe_out`, `coe_inv`), mathlib `MeromorphicOn.divisor_inv`.
- **Hypotheses**: `U` preperfect.
- **Uses from project**: `divisor_coe`, `meromorphicOn_out`, `coe_out`, `coe_inv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 525–527, proof body ≈ 2 lines
- **Notes**: unused in project.

### `def MeromorphicOn.GermRing.toNF`
- **Type**: `(a : germRing 𝕜 U) : 𝕜 → 𝕜`
- **What**: the canonical normal-form representative of a germ.
- **How**: `toMeromorphicNFOn (out a) U`.
- **Hypotheses**: none.
- **Uses from project**: `out`
- **Used by**: `meromorphicNFOn_toNF`, `coe_toNF`, `toGermRingHom_toNF`, `eqOn_toNF_of_meromorphicNFOn`, `MeromorphicField.toFun`
- **Visibility**: public
- **Lines**: 539
- **Notes**: mathlib `toMeromorphicNFOn` (`Mathlib/Analysis/Meromorphic/NormalForm.lean:656`).

### `theorem MeromorphicOn.GermRing.meromorphicNFOn_toNF`
- **Type**: `(a : germRing 𝕜 U) : MeromorphicNFOn (toNF a) U`
- **What**: the canonical representative is in normal form.
- **How**: mathlib `meromorphicNFOn_toMeromorphicNFOn`.
- **Hypotheses**: none.
- **Uses from project**: `toNF`, `out`
- **Used by**: `toGermRingHom_toNF`, `eqOn_toNF_of_meromorphicNFOn`, `MeromorphicField.meromorphicNFOn_toFun`
- **Visibility**: public
- **Lines**: 542–543
- **Notes**: —

### `theorem MeromorphicOn.GermRing.coe_toNF`
- **Type**: `(a : germRing 𝕜 U) : ((toNF a : 𝕜 → 𝕜) : Germ _ 𝕜) = a`
- **What**: the canonical representative represents.
- **How**: `← coe_out`, mathlib `toMeromorphicNFOn_eqOn_codiscrete` + `Germ.coe_eq`.
- **Hypotheses**: none.
- **Uses from project**: `toNF`, `coe_out`, `meromorphicOn_out`
- **Used by**: `toGermRingHom_toNF`, `eqOn_toNF_of_meromorphicNFOn`, `MeromorphicField.toFun_injective`
- **Visibility**: public
- **Lines**: 546–550, proof body ≈ 2 lines
- **Notes**: `@[simp]`.

### `theorem MeromorphicOn.GermRing.toGermRingHom_toNF`
- **Type**: `(a : germRing 𝕜 U) : toGermRingHom ⟨toNF a, (meromorphicNFOn_toNF a).meromorphicOn⟩ = a`
- **What**: `toNF` is a set-theoretic section of the quotient map.
- **How**: `Subtype.ext (coe_toNF a)`.
- **Hypotheses**: none.
- **Uses from project**: `toGermRingHom`, `toNF`, `meromorphicNFOn_toNF`, `coe_toNF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 553–555
- **Notes**: unused in project.

### `theorem MeromorphicOn.GermRing.eqOn_toNF_of_meromorphicNFOn`
- **Type**: `(hU : IsOpen U) {a} (h₁g : MeromorphicNFOn g U) (h₂g : (g : Germ _ 𝕜) = a) : Set.EqOn g (toNF a) U`
- **What**: uniqueness of normal-form representatives on open sets.
- **How**: codiscrete agreement (`Germ.coe_eq`, `coe_toNF`) → punctured-nhd agreement (`eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE`) → full-nhd agreement (mathlib `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`) → pointwise (`Filter.EventuallyEq.eq_of_nhds`).
- **Hypotheses**: `U` open; `g` normal form representing `a`.
- **Uses from project**: `eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE`, `coe_toNF`, `meromorphicNFOn_toNF`, `toNF`
- **Used by**: `MeromorphicField.toFun_ofMeromorphic`
- **Visibility**: public
- **Lines**: 560–570, proof body ≈ 8 lines
- **Notes**: the key uniqueness statement of the file.

### `instance UpperHalfPlane.instFactIsPreconnectedUpperHalfPlaneSet`
- **Type**: `Fact (IsPreconnected upperHalfPlaneSet)`
- **What**: the open upper half-plane is preconnected (as a `Fact`).
- **How**: `(convex_halfSpace_im_gt 0).isPreconnected`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `MeromorphicField` (enables `instField`/`instNontrivial` on `germRing ℂ upperHalfPlaneSet`)
- **Visibility**: public
- **Lines**: 581–582
- **Notes**: global `Fact` instance; mathlib has `isOpen_upperHalfPlaneSet` (`UpperHalfPlane/Basic.lean:266`) but no `isPreconnected_upperHalfPlaneSet` (searched `IsPreconnected|IsConnected` + `upperHalfPlaneSet`). Better: a plain lemma + local `Fact`.

### `instance UpperHalfPlane.instFactNontrivialUpperHalfPlaneSet`
- **Type**: `Fact upperHalfPlaneSet.Nontrivial`
- **What**: the upper half-plane has two distinct points (`I`, `2I`).
- **How**: explicit witnesses; `congrArg Complex.im` + `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `MeromorphicField` (same as above)
- **Visibility**: public
- **Lines**: 584–588, proof body ≈ 4 lines
- **Notes**: global `Fact` instance.

### `abbrev UpperHalfPlane.MeromorphicField`
- **Type**: `Type` (`:= MeromorphicOn.germRing ℂ upperHalfPlaneSet`)
- **What**: the field of meromorphic functions on ℍ modulo codiscrete agreement.
- **How**: abbreviation; `Field` instance comes from `instField` via the two `Fact`s.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicOn.germRing`, `instFactIsPreconnectedUpperHalfPlaneSet`, `instFactNontrivialUpperHalfPlaneSet`
- **Used by**: `toFun`, `meromorphicNFOn_toFun`, `ofMeromorphic`, `toFun_ofMeromorphic`, `toFun_injective`, `meromorphicNFOn_iff_exists`, `ofHolomorphic`, `toFun_ofHolomorphic`
- **Visibility**: public
- **Lines**: 592
- **Notes**: `noncomputable abbrev`; used by Basic, FieldAction, JInvariant, Congruence and four Cox files.

### `def UpperHalfPlane.MeromorphicField.toFun`
- **Type**: `(a : MeromorphicField) : ℍ → ℂ`
- **What**: the canonical representative restricted to ℍ.
- **How**: `fun τ ↦ toNF a τ`.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicField`, `MeromorphicOn.GermRing.toNF`
- **Used by**: `meromorphicNFOn_toFun`, `toFun_ofMeromorphic`, `toFun_injective`, `meromorphicNFOn_iff_exists`, `toFun_ofHolomorphic`
- **Visibility**: public
- **Lines**: 599
- **Notes**: no `toFun_zero/_one/_algebraMap/_neg` companions in this file (`toFun_algebraMap` for holomorphic functions lives in FieldAction.lean).

### `theorem UpperHalfPlane.MeromorphicField.meromorphicNFOn_toFun`
- **Type**: `(a : MeromorphicField) : MeromorphicNFOn (toFun a ∘ ofComplex) upperHalfPlaneSet`
- **What**: the canonical representative, extended by `ofComplex`, is in normal form on ℍ.
- **How**: `meromorphicNFAt_congr` with mathlib `eventuallyEq_coe_comp_ofComplex` transports `meromorphicNFOn_toNF`.
- **Hypotheses**: none.
- **Uses from project**: `toFun`, `MeromorphicOn.GermRing.meromorphicNFOn_toNF`
- **Used by**: `meromorphicNFOn_iff_exists`
- **Visibility**: public
- **Lines**: 602–607, proof body ≈ 4 lines
- **Notes**: —

### `def UpperHalfPlane.MeromorphicField.ofMeromorphic`
- **Type**: `(f : ℍ → ℂ) (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) : MeromorphicField`
- **What**: the germ of a meromorphic function on ℍ.
- **How**: `toGermRingHom ⟨f ∘ ofComplex, hf⟩`.
- **Hypotheses**: `f ∘ ofComplex` meromorphic on ℍ.
- **Uses from project**: `MeromorphicOn.toGermRingHom`, `MeromorphicField`
- **Used by**: `toFun_ofMeromorphic`, `meromorphicNFOn_iff_exists`, `ofHolomorphic`
- **Visibility**: public
- **Lines**: 611–613
- **Notes**: missing round-trip lemma `ofMeromorphic (toFun a) _ = a` and `ofMeromorphic_add/_mul`.

### `theorem UpperHalfPlane.MeromorphicField.toFun_ofMeromorphic`
- **Type**: `{f} (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) : toFun (ofMeromorphic f hf.meromorphicOn) = f`
- **What**: a normal-form function is its own canonical representative.
- **How**: `eqOn_toNF_of_meromorphicNFOn isOpen_upperHalfPlaneSet` at each `τ` (`τ.im_pos`), `funext`.
- **Hypotheses**: `f` in normal form.
- **Uses from project**: `toFun`, `ofMeromorphic`, `MeromorphicOn.GermRing.eqOn_toNF_of_meromorphicNFOn`
- **Used by**: `meromorphicNFOn_iff_exists`, `toFun_ofHolomorphic`
- **Visibility**: public
- **Lines**: 616–623, proof body ≈ 4 lines
- **Notes**: `@[simp]`.

### `theorem UpperHalfPlane.MeromorphicField.toFun_injective`
- **Type**: `Function.Injective toFun`
- **What**: canonical representatives determine the field element.
- **How**: `Subtype.ext`, `← coe_toNF`, `Germ.coe_eq`, `filter_upwards [self_mem_codiscreteWithin …]`.
- **Hypotheses**: none.
- **Uses from project**: `toFun`, `MeromorphicOn.GermRing.coe_toNF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 626–631, proof body ≈ 4 lines
- **Notes**: used by Cox/ModularFunctionField.lean and Cox/UpperHalfPlaneFunctionField.lean.

### `theorem UpperHalfPlane.MeromorphicField.meromorphicNFOn_iff_exists`
- **Type**: `(f : ℍ → ℂ) : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet ↔ ∃ a : MeromorphicField, toFun a = f`
- **What**: characterisation of the image of `toFun`: exactly the normal-form functions.
- **How**: `ofMeromorphic`/`toFun_ofMeromorphic` and `meromorphicNFOn_toFun`.
- **Hypotheses**: none.
- **Uses from project**: `ofMeromorphic`, `toFun_ofMeromorphic`, `meromorphicNFOn_toFun`, `toFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 635–642, proof body ≈ 6 lines
- **Notes**: this is what `ModularFunction.meromorphic'` (Basic.lean:33) packages existentially.

### `def UpperHalfPlane.MeromorphicField.ofHolomorphic`
- **Type**: `(f : ℍ → ℂ) (hf : MDiff f) : MeromorphicField`
- **What**: the germ of a holomorphic function.
- **How**: `ofMeromorphic` with meromorphy from mathlib `mdifferentiable_iff` → `AnalyticOnNhd` → `meromorphicOn`.
- **Hypotheses**: `f` holomorphic on ℍ.
- **Uses from project**: `ofMeromorphic`
- **Used by**: `toFun_ofHolomorphic`
- **Visibility**: public
- **Lines**: 645–647
- **Notes**: used by FieldAction, JInvariant, Cox/ModularPolynomial/Construction, Cox/ModularFunction/LevelJ.

### `theorem UpperHalfPlane.MeromorphicField.toFun_ofHolomorphic`
- **Type**: `(f : ℍ → ℂ) (hf : MDiff f) : toFun (ofHolomorphic f hf) = f`
- **What**: holomorphic functions are their own canonical representatives.
- **How**: `toFun_ofMeromorphic` with normal form from mathlib `AnalyticOnNhd.meromorphicNFOn`.
- **Hypotheses**: `f` holomorphic.
- **Uses from project**: `toFun_ofMeromorphic`, `ofHolomorphic`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 650–654
- **Notes**: `@[simp]`.

## File Summary
- Total declarations: 65 (12 defs/abbrev, 46 lemmas/theorems, 7 instances, 0 other). The anti-skim grep reports 67 because two DOCSTRING lines begin with the word `instance` (line 191 ``instance `MeromorphicOn.GermRing.instField` available…`` and line 351 `instance for the ring of meromorphic germs…`); both are prose, not declarations.
- Key API (used by 3+ others in the file): `MeromorphicOn.germRing`, `mem_germRing_iff`, `GermRing.out`, `meromorphicOn_out`, `coe_out`, `instance Inv`, `toNF`, `meromorphicNFOn_toNF`, `coe_toNF`, `divisor_coe`, `MeromorphicField`, `MeromorphicField.toFun`, `ofMeromorphic`
- Unused declarations (not used by anything in this file): `Filter.codiscreteWithin_neBot_iff`, `mem_subring_iff`, `toGermRingHom_surjective`, `coe_div`, `isField`, `isDomain`, `coe_constRingHom`, `constRingHom_injective`, `algebraMap_eq_constRingHom`, `orderAt_mul`, `divisor_mul`, `divisor_inv`, `toGermRingHom_toNF`, `toFun_injective` (used by Cox), `meromorphicNFOn_iff_exists` (used by Basic/Congruence/Cox), `toFun_ofHolomorphic` (used by FieldAction/JInvariant/Cox). Of these, the first thirteen are unused ANYWHERE in the project (grep -rlw over XYin).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `mul_inv_cancel` ≈ 16 lines)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Per-declaration mathlib status (all grep-verified against the pinned source):
  - `Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE`, `…eventuallyEq…`, `…_iff_forall_…` (×2) — NOT in mathlib; built from `mem_codiscreteWithin_iff_forall_mem_nhdsNE` (`Mathlib/Topology/DiscreteSubset.lean:213`). Clean upstream candidates for `DiscreteSubset.lean`.
  - `codiscreteWithin_neBot_iff`/`AccPt.`/`Preperfect.`/`IsPreconnected.codiscreteWithin_neBot` — NOT in mathlib; built on `codiscreteWithin_eq_bot_iff` (`DiscreteSubset.lean:369`), `accPt_principal_iff_nhdsWithin` (`Mathlib/Topology/ClusterPt.lean:225`), `IsPreconnected.preperfect_of_nontrivial` (`Mathlib/Topology/Perfect.lean:188`). Upstream candidates.
  - `MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall/exists_meromorphicOrderAt_eq_top`, `self_mul_inv_eventuallyEq_one_codiscreteWithin` — NOT in mathlib; built on `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin` (`Mathlib/Analysis/Meromorphic/IsolatedZeros.lean:59`), `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall` (`Order.lean:705`), `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero` (`IsolatedZeros.lean:71`).
  - `MeromorphicOn.subring`, `germRing`, all of `GermRing.*`, `orderAt`, `divisor`, `toNF` — NOT in mathlib (searched `germRing`, `MeromorphicOn.subring`, `Subring|Subalgebra` in `Mathlib/Analysis/Meromorphic/`). Building blocks present: `Filter.Germ.coeRingHom` (`Mathlib/Order/Filter/Germ/Basic.lean:600`), `Germ.instInv` (:458), `Germ.coe_inv` (:461), `Germ.coe_div` (:471), `Germ.instNontrivial` (:528), `Germ.instModule` (:656), `Pi.constRingHom` (`Mathlib/Algebra/Ring/Pi.lean:167`), `meromorphicOrderAt_congr`/`_mul` (`Order.lean:261/429`), `divisor_of_eventuallyEq_codiscreteWithin_preperfect` (`Divisor.lean:101`), `MeromorphicOn.divisor_mul`/`divisor_inv` (`Divisor.lean`), `toMeromorphicNFOn` (`NormalForm.lean:656`), `toMeromorphicNFOn_eqOn_codiscrete` (:685), `meromorphicNFOn_toMeromorphicNFOn` (:729), `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds` (:178), `Filter.EventuallyEq.eq_of_nhds` (`Mathlib/Topology/Neighborhoods.lean:153`), `AnalyticOnNhd.meromorphicNFOn` (:525), `eventuallyEq_coe_comp_ofComplex` (`UpperHalfPlane/Topology.lean:184`), `mdifferentiable_iff` (`UpperHalfPlane/Manifold.lean:79`).
- Field construction (question b): the project does NOT hand-roll a `Setoid`; it uses `Filter.Germ (codiscreteWithin U) 𝕜` and takes the `Subring.map` image of meromorphic functions (line 231–233). `Filter.Germ.instField`/`instDivisionRing` (`Mathlib/Order/Filter/FilterProduct.lean:55,65`) require an `Ultrafilter`, so the full germ ring along `codiscreteWithin` is not a field (functions supported on a non-discrete, non-codiscrete set are zero divisors) — restricting to the meromorphic image is necessary, and this is the idiomatic route. Two refinements: (1) mathlib lacks `Algebra R (Germ l A)` (only `Germ.instModule`); adding `Filter.Germ.instAlgebra` (via `coeRingHom ∘ Pi.constRingHom`, compatible with `instModule`) would let `germRing` be a `Subalgebra 𝕜 (Germ …)` and delete `constRingHom`/`instAlgebra`/`algebraMap_eq_constRingHom` (lines 427–448); (2) `GermRing.nontrivial` (302–307) is `Germ.instNontrivial` + `Subring.instNontrivial` (`Mathlib/Algebra/Ring/Subring/Defs.lean:365`) given a `NeBot` instance.
- `mem_germRing_iff` (236) is `Subring.mem_map`; `toGermRingHom_surjective` (250) is the range-restriction surjectivity of `Germ.coeRingHom`.
- No manual ε-δ / bound patterns in this file.

### Missing API / repeated patterns
- Repeated representative-swap fragment `rw [X_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b)) (by push_cast [coe_out]; rfl)]` at 471–472 (`orderAt_mul`) and 518–519 (`divisor_mul`): a lemma `coe_out_mul : ((out a * out b : 𝕜 → 𝕜) : Germ _ 𝕜) = a * b` (and `_inv`, cf. 526) would collapse these.
- Missing companions: `orderAt_one`, `orderAt_inv`, `orderAt_algebraMap`, `orderAt_add_ge_min`, packaging as `AddValuation` (promised by docstring 483–484); `divisor_one`, `divisor_div`, `divisor_algebraMap`; `toFun_zero`, `toFun_one`, `toFun_neg`, `toFun_algebraMap` (only the `HolomorphicFunction` version exists, FieldAction.lean:68), `ofMeromorphic_toFun` (round trip, immediate from `coe_toNF`), `ofMeromorphic_add/_mul` (only hold via `toGermRingHom.map_add`).
- The four codiscrete lemmas are used in FieldAction.lean:83,85 — general enough to move to a `Topology`-level helper file (or upstream).

### Junk candidates
- Unused anywhere in project: `Filter.codiscreteWithin_neBot_iff` (97), `mem_subring_iff` (219), `toGermRingHom_surjective` (250), `coe_div` (281), `isField` (344), `isDomain` (366), `coe_constRingHom` (431), `constRingHom_injective` (438), `algebraMap_eq_constRingHom` (447), `orderAt_mul` (470), `divisor_mul` (515), `divisor_inv` (525), `toGermRingHom_toNF` (553) — port residue from ProjectVD; API-complete but dead.
- Five concatenated module docstrings each saying "This file …" (lines 29–35, 81–91, 121–131, 183–199, 372–390) and five repeated `open Filter Set Topology` (37, 93, 133, 201, 392) with re-declared `variable` blocks (39, 95, 135–137, 203, 394): merge artefacts; one header should remain. Header (1–5) attributes the whole file to Kebekus although lines 573–658 are new project code.
- Stale docstring reference at line 73 (`eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE` does not exist).
- Anonymous instances at 266, 276, 309, 445 get very long auto-names (e.g. `instNontrivialSubtypeGermCodiscreteWithinMemSubringGermRingOfIsPreconnectedOfFactNontrivial`).

### Moral duplicates within this batch
- `GermRing.div_eq_mul_inv` (279) / `GermRing.inv_zero` (289) restate what `instField` supplies afterwards (`div_eq_mul_inv`, `inv_zero`) — kept only because they are needed before the `Fact` hypotheses; acceptable but could be inlined into `instField`.
- `nontrivial` (302) vs the `Fact` instance (309): same fact in two packagings.
- `eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE` (75) vs `Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE` (63): the former is the latter at `p y := f y = g y` (kept for `=ᶠ` notation).
- `MeromorphicField.toFun_injective` (626) has the same skeleton as `FieldAction.holomorphicToMeromorphic_injective` and `Basic.toMeromorphicField_injective` (all reduce to `Subtype.ext`/`DFunLike.ext'` + `congrArg toFun`).

### Generalization notes
- Sections (i)–(v) are already generic (`NontriviallyNormedField 𝕜`, `f : 𝕜 → E` where possible). `subring`/`germRing` are stated for `𝕜 → 𝕜`; a `𝕜'`-valued version (`NormedAlgebra 𝕜 𝕜'`) is possible since `MeromorphicOn.mul/inv` are available there (cf. line 135–137 variables), but not needed by the project.
- The ℍ section fixes `ℂ`; nothing there uses more than `IsOpen upperHalfPlaneSet`, `IsPreconnected`, `Nontrivial`, so a `MeromorphicField` over any open connected `U ⊆ ℂ` (with `ofComplex`-style retraction) would be the same code.
