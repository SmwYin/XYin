# 模多项式与 Y₀(N)：独立模型、已验证联系和几何缺口

本目录保留两组实验。本地六个模块使用 XYin 当前固定的 Lean/mathlib 环境，
参数为 `N : ℕ+`，底域为 ℂ。`AINTLIBDrafts/` 则直接导入实际 AINTLIB 对象，
在独立固定版本环境中编译：AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`、mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`、Lean `4.35.0-rc3`。
XYin 的工具链和依赖均未改动；两组模块不能在现有 XYin 环境中混合导入。

## 正确的数学目标

令 `A_N = ℂ[X][Y] / (Φ_N)`，`C_N = Spec A_N`。这里采用本地变量约定：
内层变量 `C X` 是 j，外层 `X` 是 j_N = j(Nτ)。我们所期望的几何映射是

```text
ν : Y₀(N)_ℂ → C_N,
(E, C) ↦ (j(E), j(E/C)),
[τ] ↦ (j(τ), j(Nτ)).
```

一般的正确结论是 Y₀(N) 为这个平面模型的 normalization，ν 为 finite birational
morphism，并在 C_N 的非奇异部分给出 isomorphism。不能直接把 raw plane model
定义为已有 coarse moduli scheme。Milne 的
[课程讲义 §6–8、§10](https://www.jmilne.org/math/CourseNotes/MF.pdf)
明确区分 Y₀(N) 与模多项式平面曲线，并说明非奇异部分的识别。

这一差别在实际点上也会出现：N = 2 时，(-3375, -3375) 是平面曲线的奇点，
在 Y₀(2) 上有两个复点映到它。
[Loeffler 的官方习题解答，第 1 页 Q1–Q2](https://warwick.ac.uk/fac/sci/maths/people/staff/david_loeffler/teaching/modularcurves/solutions2.pdf)
给出显式计算。这是本轮核查的数学反例参考，不是本轮新添的 Lean 反例证明。

## 本地已有的关键输入

- `Cox.theorem_11_23`：Φ_N 的复零点恰好对应 cyclic index-N lattice inclusions 的
  两个 j 值。该命题包含存在性，不声称这两个数唯一决定 inclusion 的同构类。
- `Cox.modularPolynomialC_map_eq_minpoly`：Φ_N 在 `RatFunc ℂ` 上是 j_N 的最小多项式。
- `Cox.irreducible_map_modularPolynomialC`：该最小多项式不可约。
- `Cox.theorem_11_9_ii_subfield`：Γ₀(N) 的 modular-function field 正是 ℂ(j)(j_N)。

这些输入比单纯知道 Φ_N(j, j_N) = 0 更强。最小多项式刻画全部代数关系，
field generation 则保证比较涵盖全部 modular functions。

## 实验中的各层联系

| 文件 | 目标及接口 | 数学意义 |
| --- | --- | --- |
| `PlaneModel.lean` | `evalJLevel_eq_zero_iff`、`definingIdeal_eq_ker`、`planeEmbedding_injective`、`planeScheme_isIntegral` | 独立 quotient ring 的 defining ideal 恰为 evaluation kernel；实际 affine scheme 为 integral |
| `OrbitMap.lean` | `jPair_smul`、`jPair_surjective`、`orbitMap_surjective` | 从实际 Γ₀(N) orbit quotient 满射到模多项式零点；没有虚构 injectivity |
| `ComplexPoints.lean` | 平面零点与 ℂ-valued algebra/scheme points 的联系 | 使用 over-Spec ℂ 的 morphisms，区分 geometric points 与 underlying prime spectrum |
| `FieldPresentation.lean` | `polynomialJLevelEquiv`、`polynomialModularEquiv`、`polynomialFunctionField_finrank` | 从独立 AdjoinRoot presentation 得到实际 modular field；根、系数、度数都有检查 |
| `FractionField.lean` | `planeFractionModularEquiv` | 独立 A_N 的 fraction field 与 Γ₀(N) modular functions 的 ℂ-algebra equivalence |
| `SchemeField.lean` | `planeSchemeModularEquiv` | 使用 mathlib 的实际 generic-point stalk `C_N.functionField`，并检查两个 geometric coordinates |

汇总模块还将 orbit map 与真正 scheme-point equivalence 组合为
`orbitSchemePointMap`，并证明其满射性。这样，零点 subtype 与真正的 complex-valued
scheme points 之间的桥梁也包含在最终 API 中。

函数域结论不需要先证明 normalization，因为 normalization 不改变函数域。
它也不把 modular function 的解析条件改成“属于这个函数域”：右端仍使用本项目独立的
manifold-meromorphy predicate、invariance 和 exponential cusp condition；比较是后证明的。

只知道函数域同构不能确定一个指定开放曲线的所有点，也不能证明指定 scheme 的
isomorphism。尤其不能把 Γ₀(N) quotient 的点集定义成 j-pairs：上面的 CM 例子说明
这样会丢失分支。

## 已接到实际 AINTLIB 对象的部分

令 `Y` 是 `xFullNaive` 所选的实际 full-level representing scheme，`H = borel N`，
`B = Γ(Y, ⊤)^H`。这轮已经直接使用实际 `YZeroCoarse` 证明

```text
YZeroCoarse ≅ Spec B,
Γ(YZeroCoarse, ⊤) ≅ B,
π* : Γ(YZeroCoarse, ⊤) → Γ(Y, ⊤) = 上述同构之后的字面包含映射。
```

这不是另建一个类似的对象后沿用相同名称：投影、结构映射、作用和同构全部使用
`YZeroCoarse` 定义中同一个 `xFullNaiveRepr`。它们的关键依赖已通过公理检查。

| 文件 | 已证明的实际内容 | 使用方式与范围 |
| --- | --- | --- |
| `YZeroCoarseInvariantSpec.lean` | 上述 actual scheme/ring 同构及投影拉回公式 | 将 coarse 全局截面计算化为 literal Borel invariant subring 计算；不要求 fine scheme 连通或 integral |
| `GeometricJ.lean` | 由局部 pointed Weierstrass 模型粘合正则 j，任意 local presentation 的限制公式和自然性 | 只需 affine base 上的几何 elliptic curve；与 level/coarse moduli 无关，可独立复用 |
| `ModelGeometricJ.lean` | 任意交换环上的 actual projective Weierstrass model 的 explicit top presentation，geometric j = ΓSpecIso.inv(W.j) | 给定 W 的实际模型，base 与 zero 兼容性均验证；没有 field/domain/characteristic 假设 |
| `FieldGeometricJ.lean` | 任意域上的 global pointed Weierstrass presentation、elliptic model 和 j 值一致性 | 复用上游 `GlobalChartOverField` 的 top presentation，再把系数送回 k；不要求代数闭、特征零或 level structure |
| `YZeroCoarseJ.lean` | actual `sourceJ : YZeroCoarse → Spec R[X]`，投影和底环三角，以及 X 拉回等于每个 local model 的 Weierstrass j | 从 actual universal curve 的几何 j 出发，再用 categorical quotient 唯一性下降；未借用 uniformization 或商曲线 E/C |
| `YZeroCoarseJInvariants.lean` | `R[X] → B`，X 是实际 fine invariant j，C(a) 是实际结构映射给出的常数；Spec 同构也保持底环 | 提供 ring 与 scheme 两种 API 的桥梁；X 对应的 invariant section 另行证明 invariance |
| `YZeroCoarseFiniteType.lean` | actual fine smoothness；在 Noetherian R 上 B finite type、Noetherian，actual coarse map 有限型 | 用 finite-group invariant inclusion 的 integrality 和 Artin–Tate；无 domain 假设；ℂ 上 level 的 invertibility 自动满足 |
| `YZeroCoarseProjection.lean` | actual fine-to-coarse 投影 finite、surjective；coarse 截面拉回 injective，且检测等式与消失 | 有限性只用 fine sections 的 finite type 和 invariant inclusion 的 integral；不需要底环 Noetherian，也不需要 action free |
| `YZeroCoarseReduced.lean` | domain 底环上的实际 fine sections/base、Borel invariants、coarse scheme 均 reduced | 先证明 étale/smooth algebra over domain reduced；domain 要求只落在底环，未落在 fine section ring；ℂ 自动满足 |
| `ComplexPointSeparation.lean` | 任意代数闭域上 reduced finite-type algebra 的域值点检测等式 | Jacobson 与最大理想剩余域的代数性；含 ℂ×ℂ 的非-domain sanity check |
| `YZeroCoarseComplexPoints.lean` | actual coarse 复代数点与 over-Spec ℂ scheme points 的双向对应、实际不变量截面的复点分离、源端 j 点值 | 使用实际结构映射给出的 scalar algebra；两个 inverse 和 `j(p) = φ(fineJInvariant)` 已验证 |
| `YZeroCoarsePointLifting.lean` | 每个 actual coarse 复代数点提升到 actual full-level coefficient algebra point，并给出字面的 restriction equality | 通用 lifting 引理只要求代数闭底域、injective integral inclusion、fine algebra finite type；不需要 reduced/domain |
| `YZeroCoarseFineComplexPoints.lean` | actual coarse scheme point 的 full-level lift、native elliptic curve/full marking、源端 j = native Weierstrass model j | fine algebra/scheme points 双向对应，并证明真正投影等式；full marking 来自同一 representer 的实际 homEquiv，不是新增抽象 marking record |
| `YZeroCoarsePointOrbits.lean` | coarse invariant restriction 的纤维恰为实际 Borel orbits | 通用纤维证明只要求系数环 domain；核唯一性适用于任意交换系数环，fine ring 允许零因子 |
| `YZeroCoarseComplexPointOrbits.lean` | 字面的 Borel scheme-point orbit quotient 与 actual coarse complex scheme points 等价 | 纤维定理给出 injectivity，实际点提升给出 surjectivity；不要求 action free，代表元公式由 `rfl` 验证 |
| `YZeroCoarseMarkedComplexCurves.lean` | 给定原生 E 和 full marking 后的 classifier、pointed/cartesian iso、marking 运输与 E 自身的 j；每个 E 都存在 full marking | 使用同一个实际 representability bijection；marking 的存在性复用上游已验证的 torsion-basis 定理，无新增假设记录 |
| `YZeroCoarseMarkingClassifiers.lean` | classifier 对 pointed cartesian morphism 与 positive Borel glSmul 的兼容性 | 正向 marking action 对应实际 scheme action 后复合；同底 morphism 的 base identity 从实际 base_w 推出 |
| `YZeroCoarseHomOverClassifiers.lean` | 原生 HomOver isomorphism 转成实际 cartesian EllHom，section pullback 等式与 forward mapPoint 等式互换 | 不需要 level 假设；underlying top map 精确是给定 f.hom |
| `YZeroCoarseEllIsoHomOver.lean` | 原生 EllObj iso 转成 HomOver，并与前一个 adapter 精确互逆 | 原 top map、π/zero 相容性和两条 inverse laws 全部保留；提供 IsIso 和 rfl top 公式，无 level 假设 |
| `YZeroCoarseNativeRoundtrip.lean` | 提取 fine point 的原生曲线/marking，再取 classifier 精确得到原 fine point | 使用同一个 universal pullback 与 homEquiv，检查 π、zero 和实际 marking，不另选曲线 |
| `YZeroCoarseClassifierPointIso.lean` | 相同 fine classifier 给出保持 full marking 的原生 pointed curve isomorphism | 复合同一 universal pullback 的实际同构；无需 automorphism-freeness 或 sorried coarse-points theorem |
| `YZeroCoarseNativeClasses.lean` | actual Borel GammaHClasses≃actual coarse complex scheme points；代表元、source-j、给定 marking 和任意 full lift 的逆映射公式 | 直接使用原生 Quot relation、actual Borel fiber theorem、保持 marking 的 pointed iso；不要求作用自由，不调用 sorried coarse-points theorem |
| `YZeroCoarseSourceJPolynomial.lean` | actual source-j polynomial map ℂ[X]→B 单射、零点检测与实际复点的 evaluation 公式 | 所有 j 值 + 多项式无限根唯一性；B 允许零因子，不声称 source-j finite |
| `YZeroCoarseSourceJSurjective.lean` | actual coarse source-j 在复 scheme points 和 invariant-ring algebra points 上取遍 ℂ | 用 ofJ z 的实际 projective model 与原生 classifier；不依赖上游 sorried coarse-points statement |
| `YZeroCoarseAxisGenerator.lean` | axis≅order divisor、literal ideal equality、HasExactOrder、identity fppf generator、IsCyclic 与实际 GammaZeroStructure | 任意 Spec R 上 N 可逆的 full marking；每个 actual coarse 复点有携带 Γ₀ datum 的 actual full lift；未声称 lift-independence 或 Γ₀ classes 的分类 |
| `YZeroCoarseConstantAxis.lean` | 实际 full marking 第一坐标轴、所有 test schemes 上的 subgroup image、torsion factorization、finite locally free subgroup、rank N 与 killing | 任意 Spec R 上 N 可逆时构造实际 subgroup record；actual complex 特化的 immersion 是原来的 axis；divisor generator 由独立 AxisGenerator 模块补齐 |
| `YZeroCoarseBorelAxis.lean` | 任意 scheme 上 killed section 的正向单位重编号，以及实际 Borel 换基下 axis subgroup 的 immersion ideal 不变 | 固定曲线内比较真正嵌入子群；N=5 的正向单位测试区分乘 2 与逆单位 3；尚未声称 bundled Γ₀ record 相等或 quotient-j 已下降 |
| `YZeroCoarseSubgroupQuotientGeometry.lean` | 实际原始 subgroup quotient 的 flat / surjective projection 与 universally closed structure map | 任意 scheme、elliptic curve 和带 killing datum 的 finite locally free subgroup；不调用含 sorry 的 NIsogeny quotient curve |
| `YZeroCoarseHopfGaloisLeft.lean` | 实际 canonical Galois equivalence 从 coinvariant scalars 升级为左 B-algebra equivalence | 底层 ring equivalence 与 elementary-tensor formula 保持字面相同；有限性与 étale 性另需证明 |
| `YZeroCoarseHopfFinite.lean` | coefficient algebra 有限时，实际 Hopf–Galois extension 在 coinvariants 上 module-finite；实际 free stable patch 特化 | 使用 mathlib 的 faithfully flat finite-module descent，无 domain/Noetherian 假设；尚非全局 quotient projection 有限性 |
| `YZeroCoarseHopfEtale.lean` | coefficient algebra étale 时，实际 Hopf–Galois extension 在 coinvariants 上 étale；实际 group projection 到 chart sections 的 scalar alignment | 通用结论不要求 module-finite、domain 或 Noetherian；几何 wrapper 的 `Etale G.π` 输入明确 |
| `YZeroCoarseQuasiCompact.lean` | 任意 scheme 的 QuasiCompact.of_comp_surjective，以及实际 E/G over-base quasi-compactness | 通用下降用 compact preimage 的连续像；actual wrapper 复用已有 universally closed 实例；仍未推出 properness |
| `YZeroCoarseSubgroupQuotientChartPullback.lean` | 实际 target quotient chart 的原像恰为 stable source patch，以及真实 pullback square | 使用实际 glue-overlap relation 与 saturation；给 target-local finite/étale 提供正确限制映射 |
| `YZeroCoarseLocalQuotientGeometry.lean` | 真实 local quotient projection finite，以及 `Etale G.π` 下的 local étale | 真实 coinvariant ring 与 Spec/Γ 比较；无 Noetherian/domain 假设 |
| `YZeroCoarseConstantAxisEtale.lean` | 实际常数 scheme 投影和 literal marked-axis subgroup projection étale | 任意 base scheme 的 identity components；actual full complex point 特化；未预设 quotient projection étale |
| `YZeroCoarseSubgroupQuotientFinite.lean` | actual glued/public quotient projection finite 和任意 Spec R 的 axis wrapper | 用 target chart cover 与真实 pullback square；无 Noetherian/domain/étale 假设 |
| `YZeroCoarseSubgroupQuotientEtale.lean` | `Etale G.π` 下 actual glued/public quotient projection étale；literal axis 自动满足 | 同一个 target-local 路径；不调用含 sorry 的 NIsogeny quotient upgrade |
| `YZeroCoarseSubgroupQuotientSeparated.lean` | 通用 universally-closed surjective precomposition 的 separated descent，以及 actual glued/public quotient structure map separated | 适用于任意 scheme；finite projection 给出 raw quotient 特化；无 finite-type/Noetherian/domain 假设 |
| `YZeroCoarseLocalQuotientFiniteType.lean` | actual source chart finite type、literal coinvariants/raw quotient ring finite type、真实 quotient scalar map | Artin–Tate 使用 Noetherian base patch；源 chart 的 finite type 从 E 的 smoothness 推出，无额外 source-finite-type 假设 |
| `YZeroCoarseHopfSmooth.lean` | actual chart/coinvariants/raw quotient ring smooth，以及实际 scalar ring map smooth | clean étale faithfully-flat descent；需要 subgroup projection étale 和 Noetherian base patch，无 domain 假设 |
| `YZeroCoarseSubgroupQuotientFiniteType.lean` | actual glued/public quotient structure map locally finite type、locally finite presentation、proper | 使用真实 source chart cover 与两条 structural triangles；需要 locally Noetherian base，不要求 subgroup étale |
| `YZeroCoarseSubgroupQuotientSmooth.lean` | actual glued/public quotient structure map smooth，literal marked-axis 特化 | locally Noetherian base 与 subgroup projection étale；axis 自动提供 étale；未推出相对维数或 Weierstrass model |
| `YZeroCoarseKaehlerRank.lean` | formally étale 扩张保持 Ω 的各 prime 局部秩 | 任意交换环，只要求原 Ω finite/flat；smooth 是便利 corollary，无 Noetherian/domain 假设 |
| `YZeroCoarseStandardSmoothRank.lean` | standard smooth 相对维数 n 给出各 prime 的 Ω 局部秩 n | 任意交换环；prime 自动提供 nontriviality；局部 charts 和 scheme 相对维数仍需 adapters |
| `YZeroCoarseLocallyStandardSmoothRank.lean` | locally standard smooth 相对维数 n 给出每个 prime 的 Ω 局部秩 n | 任意交换环；保留 smooth 输入用于 finite/flat Ω；采用实际 unit-span cover 和 localization prime lift |
| `YZeroCoarseSubgroupQuotientIntegral.lean` | 通用 flat-surjective reduced/integral descent，及 actual E/G over-field integrality | 任意域与实际 killed subgroup；无需 Noetherian、étale 或代数闭假设；不等于 moduli scheme 的 integrality |
| `YZeroCoarseStandardSmoothRankConverse.lean` | standard smooth algebra 的单个 prime 秩 n 推出其相对维数 n | prime 提供 nontriviality，无额外域假设 |
| `YZeroCoarseSmoothRankCriterion.lean` | smooth algebra 的常恒 Ω 局部秩 ⇔ Locally standard smooth 相对维数 | 实际 unit-span cover；含零环任意 n sanity，无 Noetherian 假设 |
| `YZeroCoarseChartKaehlerRank.lean` | actual source chart 的 Ω 局部秩恒为1 | 来自 E 的原生 relative-dimension-one appLE，无额外 chart 标准性假设 |
| `YZeroCoarseKaehlerRankDescent.lean` | faithfully-flat formally-étale extension 的常恒 Ω 秩下降 | 原 Ω finite/flat，不要求 domain、Noetherian 或全局 standard smooth |
| `YZeroCoarseChartCoinvariantsKaehlerRank.lean` | actual coinvariant chart 的 Ω 局部秩1 | 真实 Hopf–Galois faithful flatness；free patch、étale subgroup 和 Noetherian patch 明确 |
| `FiniteFunctionField.lean` | finite dominant integral-scheme map 的实际函数域拉回有限 | literal germs 与 fraction-ring base change，保留原生 scalar algebra，无 genus 假设 |
| `YZeroCoarseSubgroupQuotientFunctionField.lean` | actual raw/public/axis quotient 的 native finite injective field pullback | 任意域，无 étale、Noetherian、代数闭或 quotient model 假设 |
| `FunctionFieldFormallyUnramified.lean` | formally unramified dominant morphism 的 native generic-stalk map formally unramified | 两端仅 irreducible；integral 时才是 field map，不代表 places theorem |
| `YZeroCoarseChartQuotientRelativeDimension.lean` | actual coinvariants 及 raw quotientBaseHom 局部 standard smooth 相对维数1 | 沿真实 base-algebra equivalence 保持 literal scalar，需 free patch / subgroup étale / Noetherian patch |
| `YZeroCoarseSubgroupQuotientRelativeDimension.lean` | actual raw/public/axis quotient structure map smooth relative dimension1 | actual source cover + dimension1与开嵌入dimension0复合；需 locally Noetherian base / subgroup étale，无 genus/model 输入 |
| `FunctionFieldEtale.lean` | finite dominant formally-unramified integral morphism 的 literal native field pullback étale | 任意特征，有限型 over field 给出有限 presentation，无额外 scalar tower |
| `YZeroCoarseSubgroupQuotientFunctionFieldEtale.lean` | actual raw/public/axis quotient 的 native field pullback étale | 任意域，subgroup étale；axis 自动满足，无额外 Noetherian 或 quotient model 假设 |
| `NativeFieldWeierstrassModel.lean` | actual native E 到 literal-k fieldWeierstrassModel 的 scheme 同构及 over-base 等式 | 任意域，从已有 local presentation 与真正 coefficient base-change iso 构造；不是 quotient model 构造 |
| `UpstreamAudit.lean` | actual `YZeroCoarse`、所选 representability、affineness、quotient lift 的公理检查 | 检查所用实际依赖，而非仅扫描新增文件是否写了 sorry |

目前的便利性主要在于：使用 scheme API 时可以直接写 `yZeroSourceJ`；需要计算时，
`yZeroJPolynomialHom_X` 和 `yZeroJPolynomial_C` 给出变量与常数，
`yZeroSectionsIso_hom_comp_inclusion` 把所有 coarse 截面的拉回换成固定子环包含。
不用展开 quotient gluing、所选 representer 或 sheaf atlas 来做每一次计算。
`yZeroPr_appTop_eq_zero_iff` 则把 coarse 截面的消失归约到 fine 截面的消失。
`yZeroInvariantSpecIso_hom_comp_sourceJ` 明确证明 scheme 上的 source-j 就是
`R[X] → B` 所诱导的谱映射，提供实际点值计算所需的兼容性。

一般性方面，scheme/ring 桥梁适用于任意交换底环上的 `N ≥ 3` 且 N 可逆；
有限型的 Artin–Tate 步骤额外需要底环 Noetherian。
几何 j 的 affine-base 限制来自当前粘合证明使用 affine intersections，
不是 j 本身只能在 affine schemes 上定义。推广至有 affine diagonal 的 schemes，
再至任意 schemes 的 affine refinements，是独立的合理泛化；这轮没有以更一般的
未证明定义替代实际测试。

在 ℂ 上，`yZeroJPolynomialHom_complex_injective` 已证明 `ℂ[X] → B` 单射：
每个 z 都来自一个实际 coarse point，故多项式关系可在所有 z 上求值，
再由无限根唯一性消除。此证明没有把 B 当成整环，也没有将结论无条件推广到任意 R。
特别是 GL₂ full-level scheme 在 ℂ 上可能有不同 Weil-pairing components；
不能通过假设它 integral 来省掉粗商的连通性/整性证明。

reducedness 的证明补齐了用复点检测 regular-section 等式的一个必要条件。
这里的 reduced 表示无非零幂零元，允许不连通，也允许零因子；它与 domain 或 normal
的结论不同。有限型、reducedness 和复点分离都不能自行产生缺失的 quotient-j
或证明 Φ_N 的点值恒等式，它们使那条恒等式一旦证明后可以正当提升为全局等式。

## 接到模多项式还需要什么

1. source-j 及其 Borel descent 已完成。还要在 fine Y(N) 上构造 quotient-j，
   证明 Borel invariance，再使用 `coarsePr_existsUnique_lift` 降到 `YZeroCoarse`。
2. 将 scheme 上的这两个 j 与本地 lattice/analytic j 比较，证明 Φ_N vanishes，得到
   指向本实验 C_N 的实际 morphism。
3. 证明该 morphism finite、birational，并证明源 normal，最后使用 normalization
   的唯一性得到所要求的 scheme isomorphism。

上游已有真实 categorical quotient API，也有 fine Y(N) 的 smooth affine theorem。
但是，[`Coarse.lean` 的 j-compatible points statement](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/Moduli/Coarse.lean#L113)
仍有 `sorry`。直接使用其 E/C elliptic-curve upgrade 还会经过
[`NIsogeny.lean:2957–2973`](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/GroupScheme/NIsogeny.lean#L2957)
中 smoothness、properness、local Weierstrass presentation 的三个实际 `sorry`。
若走这条路线，需要补齐这些定理，或提供特征零下的独立构造。
本轮没有把这些缺失声明当作证明依赖。
目前已为 locally Noetherian base 上的原始商独立证明 properness，并在 subgroup
projection étale 时证明 smoothness，并已独立证明相对维数一。local Weierstrass
presentation 尚未得到；仅有 proper、smooth、维数一和 section 也不足以推出 elliptic curve，
还需 genus-one 条件或直接构造商的模型。

因此，本实验的 curve function-field theorem 不应被报告成与实际 AINTLIB
`YZeroCoarse` 的 normalization isomorphism 已完成。

## Generality 与 cusp 条件

这些本地 field/point 结果适用于全部正整数 N，包括 1、2。
现成 `YZeroCoarse` 则要求 N ≥ 3，且 N 在底环中可逆；较小 level 可考虑另选辅助
level，但还需对应的比较 API。整数模多项式的存在不自动给出任意底环上的同样模型定理；
尤其不能将本轮特征零比较无条件推广到 bad reduction。

代数函数域 ℂ(Y₀(N)) 与开放解析曲面上“所有 meromorphic functions”的 field 应区分。
后者还包含例如 exp(j) 这样的函数，其 cusp 有 essential singularity。
本项目 modular-function field 的 cusp 条件保留了恰当限制；从这个角度，
平面模型的 projective closure 再取 normalization 对应 X₀(N)，与原始问题的紧曲线
函数域相符。

## 验证记录

2026-10-03，统一目标 `lake build XYin.PhD.Test.MMeromorphic` 成功完成 **4095 jobs**。
该目标现已包含本目录全部六个 Lean 模块和汇总模块，以及之前保留的 meromorphy、
cusp、field、projective-line 测试。最终日志为
`/private/tmp/xyin-modpoly-curve-final.log`，其中没有 warning、error 或 `sorryAx`。

主要声明的 `#print axioms` 均只有 `propext`、`Classical.choice`、`Quot.sound`。
具体 checks 包括 defining ideal 的 primality、coordinate ring embedding、实际 scheme
function-field equivalence、两个 geometric coordinates、常数、逆向 roundtrip、
AdjoinRoot 的扩张次数、真正 complex scheme points 和实际 orbit map 的满射性。
`git diff --check` 也通过。

实际 AINTLIB companions 使用独立验证入口 `RunAINTLIBBridge.py`。它要求工作树和
mathlib 正好处于上面记录的 revisions，并拒绝原生来源文件的改动。随后将保留源
复制到 isolated worktree，使用 `autoImplicit = false`、
`relaxedAutoImplicit = false` 构建全部 retained targets；它检查每个 axiom print、
自身 warnings/errors，并记录源码 SHA-256、sanity 数目及编译退出状态。调用方式为：

```sh
python3 XYin/PhD/Test/ModularPolynomialCurve/RunAINTLIBBridge.py \
  --worktree /private/tmp/xyin-y0-aintlib-work \
  --elan-home /private/tmp/xyin-y0-elan \
  --lake /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake
```

这个入口不升级 XYin，不安装依赖，也不改 AINTLIB 原生证明。已有 pinned workspace
之外的复现者可先准备同 revisions 的独立 AINTLIB checkout，再替换上述路径。
2026-10-04 09:19 UTC 的最终累计验证成功，共 **9599 jobs**、**135 个保留模块**、
**1263 项逐模块公理检查**和 **258 个 sanity examples**（包含 noncomputable examples）。
各模块自身诊断为空；全部被检查声明仅使用允许的三个标准公理或其子集，
804 个不同声明中十二个无需公理。
没有 `sorryAx`、未许可公理、模块检查失败，原始来源、副本和文件清单在构建期间没有改变。
完整 source SHA-256、逐模块输出、版本和严格设置保存于
[`AINTLIBBridgeReceipt.json`](AINTLIBBridgeReceipt.json)。上游自身的历史 warnings
单独保留，不属于新增模块的零诊断声明；导入含 sorry 的文件没有被当作证明。

此检查覆盖全部此前47个模块、随后13个 rank/function-field/model 模块：
standard-smooth converse、actual source-chart rank、faithfully-flat rank descent、
actual coinvariant rank、smooth-rank criterion、actual raw chart dimension、actual
scheme relative dimension、generic finite field extension、generic formally-unramified
stalk map、generic etale field map、actual finite-injective field map、actual etale field
map、native field-model scheme iso；另有下文列出的16个rank、常数、分式域和stalk模块。
上述声明的最小假设和实际 scalar maps 已分别审阅；独立累计 provenance audit 另见
[`Cleanup/Cumulative135Verification.md`](Cleanup/Cumulative135Verification.md)，核对了
135份源码、逐模块输出、strict setups、810项 canonical artifacts、native版本和build jobs。
该 provenance audit 不替代逐个数学证明审阅。

最终135-module检查先移除全部135个实验模块自己的olean，完成新编译；源码与具名
检查记录在构建前冻结，完整逐条输出与历史99及新增36的冻结记录一致。
历史126-module检查的9590jobs/1171checks/240examples及独立审计单独保留，
原126份Lean源码在最终检查中保持byte-exact。

此前99-module检查先移除99个实验模块自己的 olean，完成新编译。Lean 本身成功，旧验证器因声明名
尾撇号漏计一项而失败；原始日志及失败记录已保留。仅修复四个名称解析表达式及
noncomputable example 计数后，重新验证缓存中的相同 Lean 证明及输出，得到历史99记录。
未改 Lean 源码、假设、公理许可范围、依赖版本或编译设置。

当前 raw quotient projection finite/flat/surjective，subgroup projection étale 时还
étale；structure map universally closed/quasi-compact/separated。后者的 locally finite
type/properness 使用 locally Noetherian base，而 smooth relative dimension1 还使用
subgroup projection étale。actual raw quotient 在任意域上 integral，native函数域拉回
finite/injective，扩张次数等于实际subgroup rank，在 subgroup étale 下还 étale。
全部点的literal stalkMap还满足最大理想扩张等式。这些都不预设 quotient elliptic model、
genus 或 target-j。原生 E 的 field-model 同构来自 E 已有的 elliptic presentation，
不能直接用于尚未构造 elliptic model 的 raw quotient。

Hopf stalk-rank、独立常数兼容、native coordinate fraction field及degree等实验，
以及其后23个源genus、整闭性、DVR/place和实际stalk兼容模块，均已纳入99-module记录。
每项历史独立检查的companions保留原来的时间/范围；新的临时实验不计入此记录。

此前 27-module / 9425-job / 218-check / 33-example 的 checkpoint 保留于
[`Checkpoints/AINTLIBBridgeReceipt27.json`](Checkpoints/AINTLIBBridgeReceipt27.json)，
39-module / 9465-job / 320-check / 55-example checkpoint 保留于
[`Checkpoints/AINTLIBBridgeReceipt39.json`](Checkpoints/AINTLIBBridgeReceipt39.json)，
47-module / 9477-job / 418-check / 77-example checkpoint 保留于
[`Checkpoints/AINTLIBBridgeReceipt47.json`](Checkpoints/AINTLIBBridgeReceipt47.json)，
60-module / 9490-job / 549-check / 105-example checkpoint保留于
[`Checkpoints/AINTLIBBridgeReceipt60.json`](Checkpoints/AINTLIBBridgeReceipt60.json)，
76-module / 9513-job / 705-check / 139-example checkpoint保留于
[`Checkpoints/AINTLIBBridgeReceipt76.json`](Checkpoints/AINTLIBBridgeReceipt76.json)，
99-module / 9563-job / 935-check / 186-example checkpoint保留于
[`Checkpoints/AINTLIBBridgeReceipt99.json`](Checkpoints/AINTLIBBridgeReceipt99.json)，
历史126-module记录亦单独保留于
[`Checkpoints/AINTLIBBridgeReceipt126.json`](Checkpoints/AINTLIBBridgeReceipt126.json)。
最终135-module记录见
[`Checkpoints/AINTLIBBridgeReceipt135.json`](Checkpoints/AINTLIBBridgeReceipt135.json)。
独立源码、输出与产物审阅保存在 `Cleanup/`。

本轮实际点桥梁的数学/API 分工见 `ActualPointBridge.md`；剩余依赖见
`YZeroCoarseComparisonGaps.md`；源代码独立审阅和三项声明的 scoped cleanup 报告
保存在 `Cleanup/`。这些报告没有声称对整个 AINTLIB 或全部新文件进行了完整 cleanup。

### 60-module checkpoint 后新增且已累计验证的结果（2026-10-04）

76-module checkpoint已覆盖后续16个模块；它们也各自通过具名严格编译及独立审阅。新增结论包括 Hopf/group/local/global quotient rank、finite-flat scheme rank与实际函数域degree的通用桥，以及actual E→E/G的degree等于subgroup rank。

另有独立几何常数的自然性与BaseAlgebra/tower/baseAlgHom、projective-model常数图、nativeκE-compatible函数域AlgEquiv、native coordinate fraction-field pack及full-constant-field下降。generic及actual quotient全部点的stalk最大理想等式也已验证。各自范围见任务板与验证记录。

### 76-module checkpoint 后新增的23个模块

实际源 E 的独立几何常数下，polynomial/RatFunc/finite/separable pack、满常数域及
intrinsic genus=1 均已证明。商 Q 的独立常数下，真实函数域拉回是 k-AlgHom，
满常数域可下降，且 Q 的函数域存在超越元素；没有假设源 x 在商中。

源及商的全部 stalk 整闭，商的非空 affine open 截面整闭。通用闭点 DVR 定理、
实际 stalk 标量塔和函数域交换图给出真正闭点的 intrinsic Place；其规范化 valuation
等于原 DVR adic valuation。实际 étale 商投影的长度定义 ramification index 为1。
在这个历史99-module阶段，尚无全部places几何对应或Riemann–Hurwitz公式。
后续闭点/place对应已证明；Riemann–Hurwitz仍未建立。

### 99-module checkpoint 后新增且已纳入126-module检查的27个模块

实际raw/public商自身的每个超越参数已给出有限RatFunc嵌入，保留结构映射定义的
常数。参数的X公式、多项式限制、AlgHom自然性以及polynomial/RatFunc塔均已检查。
旧source x若经真正标量塔下降到商，会迫使subgroup rank整除2；rank3矛盾现已
在Lean中证明，因此一般商必须使用自己的参数。

实际闭点places在dominant FU+LFT映射下的规范化valuation相等已证明，并已套到
真正étale subgroup商；目标闭点由真实finite投影自动给出。非平凡place包含实际
DVR像时等于该DVR place；properness给出真实generic/base兼容lift，有限residue
使中心为闭点。中心stalk到generic stalk的交换等式只需不可约scheme。
原生椭圆曲线所有places的residue有限性也已从完整separating pack推出。

properness与真实stalk交换式还给出闭点place恢复；原生E的每个place都有真实闭点表示。
特征零实际商所有places的residue有限，étale subgroup时也都有真实闭点表示。
separated smooth integral curve上的closedPointPlace已证明单射，不假定proper或residue。
任意域上实际étale商的每个source place都有target place，使literal函数域拉回的
normalized valuations相等。

这些逐文件正确模块名的严格检查，完整输出、源码及六项canonical产物和C文件
记录见各自 `Cleanup/` companion，现均已纳入126-module累计记录。
任务板 `YZeroCoarseTickets.md` 和 [`PlaceBridgeAnalysis.md`](PlaceBridgeAnalysis.md)
说明最小假设、API取舍及尚未完成的跨域除子/genus任务。

### 126之后新增且已纳入最终135-module检查的九个模块

`SchemeClosedPointPlaceEquiv`、`YZeroCoarseSubgroupQuotientPlaceEquiv`提供真正闭点/place
双向API；`PrincipalDivisorValuation`给出主除子系数的归一化valuation公式。
实际商的`PlaceMap`及`PlaceMapFiniteFibers`模块给出真实restriction和有限纤维。
`FinsuppFiniteFiberPullback`支持多对一映射，`PrincipalDivisorPullback`证明通用兼容。
实际`DivisorPullback`与`PrincipalDivisorPullback` wrappers分别在任意底域+Etale、
CharZero+Etale范围内实例化；所有scalar/chart输入均来自真实几何pack。
详细条件、实际API和验证记录见任务Y0-98至106及各`Cleanup/` companion。

raw E/G 的 genus、Weierstrass model、实际 target-j/Φ identity及normalization比较
仍未证明。E/G 的整闭性也不能用于断言 coarse moduli scheme 的 normality。
