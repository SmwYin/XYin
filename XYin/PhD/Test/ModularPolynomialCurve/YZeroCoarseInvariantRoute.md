# 实际 YZeroCoarse 的 invariant-ring 路线

核查的上游版本是 AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`。本文件记录与实际上游对象的连接，
不把一个自行定义的解析 quotient 改名为 `YZeroCoarse`。

## 可直接用于连接的上游构造

`ModularCurves.YZeroCoarse R N hN hinv` 是实际 representing full-level scheme
的 Borel 商。它不是抽象给定满足商性质的 scheme。

令 `Z := (xFullNaive N hN hinv).base`，`f` 为其结构映射，
`σ := (xFullNaiveRepr ...).baseSchemeAction (gammaHAut R N (borel N))`。
`RelativeInvariantSpec.lean` 的定义和定理给出：

1. `invariantsDiagram` 在基底 affine open `U` 处取
   `FixedPoints.subalgebra ℤ Γ(Z, f⁻¹U) (borel N)`；
2. `relQuotientChartι` 是该谱到实际商的 open immersion；
3. `relQuotientStruct_preimage` 把该 open immersion 的像识别为结构映射对 `U`
   的原像；
4. 对 `U = ⊤`，该原像是整个商。因此 top chart inclusion 是 isomorphism。

这给出实际对象的 affine-spectrum identification：

\[
Y_0(N)_R \cong \operatorname{Spec}\bigl(\Gamma(Y(N)_R,\mathcal O)^{B_N}\bigr).
\]

实现是 `AINTLIBDrafts/YZeroCoarseInvariantSpec.lean`。它还包含实际投影
的 commuting triangle、global-section-ring isomorphism，以及“投影的 pullback 恰是
invariant-ring inclusion”的定理。全文件已经在 pinned AINTLIB 环境编译通过，
本文件无 warning/error。实际 `yZeroInvariantSpecIso`、投影 triangle 和 section inclusion
的 `#print axioms` 均只有 `propext`、`Classical.choice`、`Quot.sound`。
不能以本地 XYin aggregate build 作为该文件的编译证书。

## source-j 的具体输出

`AINTLIBDrafts/YZeroCoarseJInvariants.lean` 将两个独立构造接起来：

- regular source-j map 来自 universal geometric elliptic curve 的局部 Weierstrass
  j-invariant，并经 sheaf gluing 成为 global regular section；
- invariant section ring 来自实际 `YZeroCoarse` 的 Borel quotient。

得到具体 ring hom

\[
R[X] \longrightarrow \Gamma(Y(N)_R,\mathcal O)^{B_N}.
\]

其 composition 与 invariant-ring inclusion，等于 universal curve 的实际
`jPolynomialHom`，不是一个假定满足此性质的 ring hom。`X` 的像等于独立构造的
`fineJInvariant`；coarse j 的 global section 在 `yZeroSectionsIso` 下也等于该
invariant section。常数通过实际 coarse structure morphism pullback，且该 ring hom
与它相容。这里没有假定 j transcendental，也没有假定这个 polynomial ring hom
injective。
该 combined 文件现已在 pinned AINTLIB 的严格单目标 Lake build 通过，
其自身无 warning/error。`X` 的识别、coarse section 与 fine invariant j 的识别、
inclusion、常数相容和谱同构 over-base 的 axiom 输出全部只有标准三公理。

`yZeroInvariantSpecIso_hom_comp_sourceJ` 还给 scheme morphism 本身的实际恒等式：
谱同构的 `hom` 后接 `Spec.map yZeroJPolynomial`，恰是原来的 `yZeroSourceJ`。
证明先沿实际 `yZeroPr` 拉回，用 invariant inclusion triangle 得到 fine `jMap`，
然后用同一个 actual coarse quotient 的唯一性比较两个 morphism；没有加入 `Epi` 假设。
这个新增定理已经由 pinned Lean binary 与实际 Lake setup 独立检查，exit 0，自身无
warning/error，且 `#print axioms` 只有标准三公理；日志为
`/private/tmp/yzero-sourcej-iso-triangle.log`。它让 ring-hom 的 `X` 计算直接转为
literal `Spec ℂ → YZeroCoarse` 点上的 source-j scheme-map 计算。

独立交叉审阅 `GeometricJ.lean` 与 `YZeroCoarseJ.lean` 的实际 proof 后，
source-j 的识别有以下明确范围：

- overlap compatibility 通过实际 atlas opens 的交集上两套 restricted
  Weierstrass presentations 的 variable change 证明，再使用结构 sheaf gluing；
- `jSection_res` 覆盖任意 `LocalPresentation`，不是仅给 chosen atlas 的公式；
- transported moduli automorphism 的 inverse 与 `SchemeAction.ofAut` 的方差一致，
  因而 actual action invariance 来自 cartesian pointed naturality；
- coarse descent 使用实际 quotient 的 `coarsePr_existsUnique_lift`，over-base
  compatibility 也用同一个唯一性定理；
- generic geometric j 目前取 affine base。两个 affine schemes 间 morphism 的
  `IsAffineHom` 自动成立，naturality 定理的该 instance 不增加实际限制；
  generic coarse 部分的 affine instance 是 local，有限群假设只在 descent 时引入。

## 为什么不能直接把全 level scheme 当作 integral scheme

AINTLIB 的全 level datum 没有固定 Weil pairing。在复数上，它一般含不同 Weil-pairing
值对应的多个连通分支。Borel 的 determinant 可交换这些分支；这使粗商有可能是 integral，
但不能把 `Y(N)` 的坐标环视为一个 domain 来取其 fraction field。

上游 `ForMathlib/SmoothCurveComponents.lean` 的说明也明确保留此 disconnected 情形，
其 theorem `injective_pi_quotient_minimalPrimes` 和 idempotent splitting API 可以用于
componentwise 论证。`FactorIntegrallyClosed.lean` 提供 componentwise integral closedness，
但其标准光滑维数一和局部 domain 条件还需真正实例化。

上游 `YFull.gammaFullNaive_representable_assembly` 给任意 representing object 的
smooth affine structure morphism。这个 smoothness theorem 本身不能替代
`YZeroCoarse` 的 connectedness、normality 或 j-finiteness。

本轮另有 `YZeroCoarseFiniteType.lean` 将此实际 smoothness 实例化：全 level 的
section ring 对 `R` finite type；它对有限 Borel invariant ring integral。
在 `R` Noetherian 时，Artin–Tate 给实际 invariant ring 对 `R` finite type，
因此该 invariant ring Noetherian，实际 coarse structure map finite type。
此文件已经严格编译与标准三公理检查。这仍不意味着 source-j map 对 `R[X]` finite。

`YZeroCoarseProjection.lean` 进一步在任意允许的交换环基底上证明实际 projection
`yZeroPr` 有限且满射，以及其 global-section pullback 单射。理由是 invariant
inclusion integral，而 fine section ring 对原基底 finite type，所以它也对 invariant
ring finite type；integral 加 finite type 给有限模。这里使用
`RingHom.FiniteType.of_comp_finiteType` 的正确方向，**不需要**基底 Noetherian。
scheme 有限性随后由已经验证的实际 spectrum triangle 及 isomorphism cancellation 得到。
section pullback 的单射性则来自 literal invariant inclusion 和 `yZeroSectionsIso`，
不是从 scheme-point surjectivity 推断的。`yZeroPr_appTop_eq_iff` 与
`yZeroPr_appTop_eq_zero_iff` 因此允许把 coarse section 的等式或消失放到实际 fine scheme 检查。
这个最终文件的 pinned direct compiler 检查已绿，自身无 warning，五个打印声明均只有
标准三公理；日志为 `/private/tmp/xyin-y0-projection-final-check.log`。
这项有限性是 **fine-to-coarse projection** 的有限性；source-j 对 j-line 的有限性仍未证明。

## 实际复点的代数提升

`YZeroCoarsePointLifting.lean` 证明每个实际 invariant ring 的 `ℂ`-algebra point
都可以提升为实际 full-level section ring 的 `ℂ`-algebra point。提升的限制等式是
literal ring-hom equality：若 `φ` 是原点，则存在 `ψ`，使

```text
ψ.toRingHom.comp actualInvariantInclusion.hom = φ.toRingHom.
```

这里 fine ring 的 `Algebra ℂ` 恰为 `fullCoefficientHom.toAlgebra`，coarse ring 的
scalar action 恰为 `yZeroInvariantAlgebra`；inclusion 的 scalar law 直接用已验证的
`yZeroInvariantCoefficientHom_comp_inclusion`。它没有任选另一种标量结构。

泛型证明适用于任意代数闭基域 `k`、任意交换 `k`-algebras `B, A`，当
`ι : B →ₐ[k] A` 单射且 integral、`A` 对 `k` finite type 时，每个 `B →ₐ[k] k`
都扩张为 `A →ₐ[k] k`。先在原点的 maximal kernel 上方用
`Ideal.exists_ideal_over_maximal_of_isIntegral` 找 maximal ideal，再用
`exists_algHom_ker_eq_of_isMaximal` 得到其 `k` 点。对
`b - algebraMap k B (φ b)` 的消失给出精确 restriction equality。
`B` 不需要 finite type；两个环都不需要 domain 或 reducedness。
`A` 的 finite-type 条件只在 maximal residue field 的代数性这一步使用；未来可以
考虑适当的 residue-algebraicity 泛化，本轮没有引入一个未验证的新假设接口。

实际 instantiation 的 fine finite type、inclusion injectivity 和 integrality 都是
对真实 AINTLIB 对象已证明的事实。文件包含 `ℂ × ℂ` 的非-domain sanity check，
已严格编译通过。最终 pinned target build exit 0，9394 jobs，target 87s，自身无
warning/error；generic lifting、实际 inclusion AlgHom 和实际 lifting theorem
的 axiom 输出均只有标准三公理。日志为 `/private/tmp/xyin-y0-point-lifting-build.log`。
其模块只 import `ComplexPointSeparation`、`YZeroCoarseFiniteType` 和 `Ideal.GoingUp`，
不与实际 scheme-point 文件形成 import cycle。

联合导入检查发现，两个文件的 anonymous local algebra instances 会生成相同的
declaration name。root 已只把本文件的 local instance 命名为
`pointLiftingFullAlgebra`、`pointLiftingInvariantAlgebra`，对应类型、实现、优先级和
实际 scalar maps 都保持一致；这项 integration 修复已审阅。上段 standalone
build 是修复前的完整证书；命名后的最终版本已通过 root 的联合依赖检查，并由
`YZeroCoarseFineComplexPoints` 的实际 artifact emission 再验证：exit 0，十一条
printed theorem 全部只含标准三公理，无 warning/error，`.olean` 为 76272 bytes。
日志为 `/private/tmp/yzero-fine-complex-points-emission.log`。

这一步输出 actual coefficient-algebra point 及其 restriction equality。独立模块
`YZeroCoarseFineComplexPoints` 已把它转换为 literal `Spec ℂ` 上的 fine scheme
point，并 pull back 实际 universal elliptic curve 及 full-level marking。每个实际
coarse complex scheme point 都有这样的 fine lift；其 coarse source-j 等于该 native
curve 的 Weierstrass j。这里没有声称取得解析 uniformization 或完整的 moduli-point
分类。

## 给定 native marked curve 到实际 coarse 点

`YZeroCoarseMarkedComplexCurves.lean` 接受实际
`E : ModularCurves.EllipticCurve (Spec ℂ)` 和它的 naive full-level marking `α`。
`complexEllObj E` 的结构映射就是 identity，classifier 则是实际选定的
`xFullNaiveRepr.homEquiv.symm α`。classifier 的 `base_w` 直接给出 over-`Spec ℂ`
的 fine scheme point；复合实际 `yZeroPr` 得到 `yZeroComplexSchemePointOfMarking`。

`complexFullMarkingNativeIso` 不是只比较 j 的同构：它是 `EllObj` 范畴中的同构，
因此包含 cartesian square 和零点相容性，且它的 base morphism 是 identity。
`complexFullMarkingNativeIso_level` 证明将 native universal marking 沿同构拉回，
恰好得到输入的 `α`。证明只用 representability 的 `homEquiv_comp`、真实的
`toPullbackAlong_pullbackAlongπ` factorization 和分类双射的 inverse identity。
没有假设一个待证明的 curve/marking comparison。

在同一个 actual coarse 点上，`yZeroComplexSchemePointOfMarking_comp_sourceJ` 给出
literal scheme-morphism equality；`yZeroComplexSourceJValue_of_marking` 再给出

```text
sourceJValue (pointOfMarking E α) = (fieldWeierstrassModel E.toEllipticCurveGeom).j.
```

这两个结论都通过上述 pointed iso 的自然性证明，右边是给定原曲线的 model，
不是仅有相同 j 的一条另行假设的曲线。source-j 值因而不依赖 marking；此处没有
证明 coarse 点本身对任意 marking 都相同。实际 classifier 仍使用 AINTLIB 当前
`N ≥ 3` 的 full-level representation。

`nonempty_complexFullMarking N E` 还去掉了调用者必须预先提供 marking 的要求。
它直接使用实际已 import 的
`ModularCurves.exists_isNaiveFullLevel_of_isAlgClosed ℂ E N hk`，其中
`hk := (complexLevelIsUnit N).ne_zero`。这个存在性接口只要求 `NeZero N`，没有
`N ≥ 3` 参数，也没有额外的 curve comparison 假设；exact upstream theorem 的
公理检查已通过。`exists_yZeroComplexSchemePoint_sourceJ_eq` 随后对每个给定 `E`
给出实际 coarse complex point，其 source-j 是该原曲线的 Weierstrass j。这个
coarse-point classifier 仍需 `N ≥ 3`，并通过前面已验证的实际 pointed iso 构造。

最终 157-line source 的 strict exact-binary compiler exit 0，无 warning/error，九条
printed checks（exact upstream theorem 和八条本文件声明）全部只有标准三公理。
level-3 sanity 一种直接输入 `P Q : E.Section` 和 `E.IsNaiveFullLevel 3 P Q`，
另一种只输入原曲线 `E`。最终 `.olean` 为 37640 bytes，retained/build source
byte-identical，sha256 为
`f8bb25f74e3b3d10868794d02e2c09be90f56738361570602733213116c28bda`。
日志为 `/private/tmp/xyin-y0-marked-complex-curves-check.log`。

## Given-curve classifier 的自然性与 Borel compatibility

`AINTLIBDrafts/YZeroCoarseMarkingClassifiers.lean` 保留两个实际接口。
`fullComplexSchemePointOfMarking_map` 说明：给定
`u : complexEllObj E ⟶ complexEllObj E'`，用实际 full-level functor 将 `E'` 的
marking 拉回后，其 fine complex classifier point 与原 `E'` 的 classifier point
相同。这里没有额外的 `u.baseHom = id` 参数：两个对象的 structure map 都为 id，
所以这个等式直接来自 `u.base_w`。`u` 本身是 cartesian pointed morphism，
不包含任意 isogeny 或 zero morphism。

`fullComplexSchemePointOfMarking_glSmul` 给出实际 scheme-morphism equality

```text
classifier (E.glSmul g L).val = classifier L.val ≫ borelAction.hom g.
```

此处是正向 `glSmul g`。`gammaHAut` 的 hom 用 `glSmul g⁻¹`，而实际
`baseSchemeAction` 使用对应 represented automorphism 的 inverse；两者相消。
证明在 actual representing object 的 `EllHom` 层用
`homEquiv_comp_transportHom` 的 inverse natural transformation 验证这个 pin，
再投影到 base morphism，没有假设 action compatibility。

retained 108-line 文件的 strict direct leaf check exit 0；两个 axiom prints
均为标准三公理，无 warning/error，两个 level-3 sanity 通过。
retained/build source byte-identical，sha256 为
`a5f2207e5493c363e7a6524c9ada1f3caa04c9452ed389f8d3be5d77c9b318d1`，
emitted `.olean` 为 25744 bytes。日志为
`/private/tmp/xyin-y0-marking-classifiers-check.log`。

## 实际原生 `GammaHClasses` 与 coarse complex points 的等价

`AINTLIBDrafts/YZeroCoarseNativeClasses.lean` 将上面的 classifier 直接下降到
AINTLIB 实际 `GammaHClasses (Spec (.of ℂ)) N (borel N)`，给出

```text
gammaHClassesComplexPoint N hN :
  GammaHClasses (Spec (.of ℂ)) N (borel N) → yZeroComplexSchemePoint N hN.
```

原始 `Quot` relation 的 witness 是 native pointed same-base isomorphism
`f : E.HomOver E'`、`g ∈ borel N`，以及两个 forward section equations。
独立模块 `YZeroCoarseHomOverClassifiers` 将这个实际 `f` 变成 cartesian pointed
`EllHom`，并用实际 pullback square 的 `lift_fst` 和 `IsIso f.hom` 的右消去
证明：forward section equation 等价于 functorial pullback equation。
本文件随后组合 classifier naturality、正向 `glSmul g` 的实际 Borel action
compatibility，以及 actual coarse fiber iff，验证 `Quot.lift` 的 well-definedness。
这里使用的 relation 是原文件的 literal relation，没有另行假设 moduli comparison。

`gammaHClassesComplexPoint_mk` 为 `rfl`，计算类代表得到其实际 coarse point。
`gammaHClassesComplexPoint_sourceJ_mk` 将这个点的 source-j 计算为给定 native
curve 的 `fieldWeierstrassModel(...).j`。

`gammaHClassesComplexPoint_surjective` 进一步证明每个实际 coarse complex point
都来自这样一个 native class。证明先用实际 coarse-to-fine lifting 得到 `q`，取实际
universal curve 的 pullback 和原生 full marking 作为 class representative，然后用
模块 `YZeroCoarseNativeRoundtrip` 中的 `fullComplexSchemePointOfMarking_native`
（声明在 main AINTLIB namespace）恢复原 fine point。这一回代证明用 literal identity base/curve
arrows 比较两种 structure-map presentation，证明每个 section 与 full marking
pullback 不变，再投影 actual representing equivalence 的自然性等式；不是额外假设。

`gammaHClassesComplexPoint_injective` 建立完整逆向关系。对原生 representatives
`(E, α)`、`(E', β)`，actual coarse fiber iff 给出 `g : borel N` 和
`classifier(E', β).val = classifier(E, α).val ≫ σ_g`。正向 action formula 因而
识别 `classifier(E, glSmul g α)` 与 `classifier(E', β)`。独立的 PointIso 模块
从这两个实际 fine classifiers 构造 `e : complexEllObj E ≅ complexEllObj E'`，
其 marking equation 是 `F.map e.hom.op β = glSmul g α`。独立 reverse adapter
将同一实际 `e.hom.top` 变成 `f : E.HomOver E'`，证明 `IsIso f.hom`，并精确
重构原 `e.hom`。两个 component pullback equations 经旧 `pullSection_eq_iff` 的
MP 方向变成 forward `f.mapPoint` equations，恰好给出原始 `GammaHClasses`
relation 的单个 witness。对任意 classes 用 `Quot.induction_on₂` 下降，对原始
witness 用 `Quot.sound`；没有把 relation 换成另一种 moduli relation。

由实际 injectivity 与 surjectivity，`gammaHClassesComplexPointEquiv` 给出

```text
GammaHClasses (Spec (.of ℂ)) N (borel N) ≃ yZeroComplexSchemePoint N hN.
```

`_mk` 和 `_sourceJ_mk` 给出原 representative 的正向 classifier 和 j 公式；
`_symm_of_marking` 从给定 curve classifier 的 coarse point 恢复原 class。
`_symm_of_full` 则将任意 actual full point 投影的逆像写成其 literal native
pullback curve/full marking 的 class；`_symm_of_lift` 同样接受 `q` 和其投影
等于指定 coarse point `p` 的证据。所以这些公式不依赖某次 chosen lift。
这里尚未将原生 Borel-full-marking classes 改写为 cyclic-subgroup moduli，也尚未
建立 target-j、modular-polynomial relation 或完整函数域比较。

最终 retained 247-line strict named leaf emission exit 0，actual `GammaHClasses` 与
`GammaHClasses.mk`、十一个 own declaration 的十三个 axiom prints 全部为标准三公理，
五个 level-3 sanity（含实际 classes/coarse-points 两侧 roundtrip）通过，无 warning/error。
retained/worktree source byte-identical，sha256 为
`90353b439ca8098e902eaed1cc32dce37ab59166727ce4f6ad40fcb415b0339b`，
最大行宽 95，`.olean` 为 43776 bytes。最终日志为
`/private/tmp/xyin-y0-native-classes-check.log`。injectivity/equivalence 的追加在首次
elaboration 即通过。upstream `Coarse.lean` 的 sorried classification 声明没有被用到；
具体公理输出直接确认这一点。

早期阶段 receipt 单独保留：第一次临时 map 检查的唯一 own warning 是局部 Prop
instance 使用 `letI`，改为 ordinary `let` 后无警告；map-only 的五个 clean checks
保留在 `/private/tmp/xyin-y0-native-classes-map-check.log`。第一轮 surjectivity
elaboration 在 `rw` 的 implicit transparency 下未展开 native curve 的基底；明确标注
`E : EllipticCurve (Spec (.of ℂ))`、`L : E.FullLevelPt N` 后同一证明通过。失败日志为
`/private/tmp/xyin-y0-native-classes-surjectivity-first-check.log`，其中占位 `sorryAx`
不属于最终 receipt。surjectivity 的最终六个 clean checks 单独保留在
`/private/tmp/xyin-y0-native-classes-surjectivity-check.log`。

## 任意 model 的 j 公式，以及实际 source-j 的满射性

`AINTLIBDrafts/ModelGeometricJ.lean` 提供两个泛型接口。对任意交换环 `A`、
`W : WeierstrassCurve A` 和 `W.IsElliptic`，`modelTopPresentation W` 给出原生
`modelEllipticCurve W` 的 whole-base local presentation；其三段 iso 来自实际
`locallyWeierstrass_projModel` construction，并验证 projection 和 zero 的兼容。
`model_jSection W` 随后给出

```text
jSection (modelEllipticCurve W).toEllipticCurveGeom = ΓSpecIso.inv.hom W.j.
```

这个公式没有 field、domain、nontrivial 或 characteristic 假设。它避免为了计算
一个明确 Weierstrass model 的 j 再去分析 chosen atlas。retained 121-line 文件只
import `GeometricJ` 和实际 `ModelRecord`；两个声明的严格检查均为标准三公理，
没有 warning/error。日志为 `/private/tmp/xyin-model-geometric-j-check.log`。

独立的 `AINTLIBDrafts/YZeroCoarseSourceJSurjective.lean` 接续这个公式。
`fieldWeierstrassModel_model_j` 在任意 field `k` 上证明所选 field model 的 j 仍是
原 Weierstrass curve 的 j：这里仅需组合 `fieldWeierstrassModel_j`、上述 formula
和 `ΓSpecIso` 的 inverse cancellation。对 `z : ℂ`，mathlib 的
`WeierstrassCurve.ofJ z` 则给出真正 elliptic 的 Weierstrass curve，且 j 等于 `z`。
将其 native model 输入前面已经证明的 given-E coarse-point existence，得到

```text
yZeroComplexSourceJValue_surjective N hN :
  Function.Surjective (yZeroComplexSourceJValue N hN)

yZeroComplexInvariantJValue_surjective N hN :
  Function.Surjective
    (fun φ : yZeroComplexAlgebraPoint N hN => φ (fineJInvariant ...)).
```

这两个实际接口只要求 `NeZero N` 和 `3 ≤ (N : ℤ)`。第二个通过原有实际
scheme/algebra-point equivalence 从第一个转换，评价的是 literal invariant
subring 中的实际 fine j；没有将 source-j surjectivity 当作额外假设。这个论证也
包含 `0` 和 `1728`，由 upstream `ofJ` 的实际分支和 `ofJ_j` 定理处理。

严格 exact-binary leaf 检查 exit 0，三个 printed checks 全部只有标准三公理，
没有 warning/error；level-3 sanity 分别直接取得任意 `z` 的 scheme point 和
algebra point。最终 source 为 78 行；日志为
`/private/tmp/xyin-y0-source-j-surjective-check.log`。第一次 invocation 只缺少
setup 中的 transitive `FineComplexPoints` artifact mapping，在 elaboration 前停止；
补入 exact existing mapping 后，上述最终 invocation 通过，proof source 未变。

这个满射性使实际 polynomial coefficient map 的 injectivity 可以通过复点评价
来证明，但本文件本身尚未宣布完整 modular-polynomial relation 或函数域同构。

## 还不能由这一步推出什么

该谱识别、source-j ring hom 和常数 compatibility 不构成 modular-polynomial
normalization theorem。还缺少：

1. quotient elliptic curve 的 regular target-j map；
2. 证明两个实际 j section 满足本地 `Φ_N`；
3. 证明所得映射 finite、birational，并为实际 invariant ring 建立适当的
   integral-closure/normality 结果。

这三步都包含数学内容。仅由 categorical quotient universal property，或仅由
已有解析函数域同构，无法推出它们。

## 信任与验证范围

本轮对 `CoarseSpace` 的本地项目 import closure 做了源码扫描：244 个项目文件、
43 个实际 `sorry` token。这个数字不能证明某个具体 theorem 依赖 `sorryAx`：
import 一个未使用的含 `sorry` declaration 不影响其他 theorem。具体 bridge 的
可信度由 pinned AINTLIB compilation 和其 `#print axioms` 输出决定。现在实际
`YZeroCoarse`、full-level representation、coarse quotient unique lift，以及本实现的
实际 `yZeroInvariantSpecIso`/投影/sections compatibility 已通过这个审计，均只有标准
三公理。
源码上，实际 `xFullNaive` 使用的是 `gammaFullNaive_rigid_and_representable` closure，
而不是较早的 held engine 声明；其 affine theorem 也有具体 recollement proof。
因此不能据 import-closure 的原始计数宣布这个实际对象带有额外公理。

已在本地 mathlib 环境单独 kernel-check 的计算包括：`f⁻¹⊤` 与 global sections
的 definitional equality，top-open inclusion 的 cancellation，inverse chart triangle，
以及 `ΓSpecIso` naturality 推导出的 pullback inclusion。其 generic invariant-quotient
实现也已在 pinned AINTLIB 的 `GenericInvariantProbe.lean` 编译通过。实际
`YZeroCoarse` 的全文件 instantiation 也已经编译通过；记录位于隔离 workspace 的
`yzero-bridge-build.log`，该 module 在 joint build 的 `[9384/9396]` 完成，
自身无 warning/error。combined source-j 文件的最终独立严格 build 记录位于
`yzero-j-invariants-final.log`，以 `[9379/9379] Built AINTLIBDrafts.YZeroCoarseJInvariants`
和 `Build completed successfully (9379 jobs)` 结束，关键 declaration 均只有
标准三公理。旧 joint log 曾包含修复前的一个 subtype projection elaboration error，
应使用这个最终 log 验证 `X` 定理。

## 最有用的后续 API

`yZeroSectionsIso_hom_comp_inclusion` 让 coarse regular section 的 pullback 化成
literal invariant-subring inclusion；`yZeroJPolynomialHom_X` 则把实际 coarse j
坐标的像化成独立构造的 fine invariant j。常数定理和
`yZeroInvariantSpecIso_hom_comp_base` 保证这种计算保留原来的 `R`-结构。
它们比仅给一个存在的谱同构更方便：下一步的 polynomial evaluation 可以直接用
ring-hom API，而不需要重新证明 chosen quotient projection 与 section-ring 同构的兼容。
