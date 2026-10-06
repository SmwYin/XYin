# 实际 coarse 复点：目前已经连接到什么

本说明使用本目录 `AINTLIBDrafts/` 中的实际 AINTLIB 对象。固定版本和构建方式见
`README.md`；这里的 `YZeroCoarse` 不是独立的模多项式平面模型。

## 三个可直接使用的接口

令 `Y` 为实际 `xFullNaive` 的 representing base，`H = borel N`，底域为 ℂ，
`N ≥ 3`。一个复点始终是 over-Spec ℂ 的 scheme morphism。

1. `yZeroComplexSchemePoint_lifts`：每个实际 coarse 复点都经实际投影提升到 Y。
   提升来自不变量环包含的 integral lying-over，以及有限型代数最大理想的
   ℂ-valued point；没有假定 fine ring 是整环。
2. `yZeroComplexSchemePointOfFull_eq_iff_borel`：两个提升具有同一 coarse image，
   当且仅当 `q.val = p.val ≫ σ(g)` 对某个实际 Borel 元素成立。
3. `fullComplexBorelOrbitEquivYZero`：由这个**字面的作用轨道关系**形成的商，
   与实际 coarse 复点集等价。关系没有定义成 coarse map 的 kernel；纤维定理
   证明它与该 kernel 相等。代表元公式由 `rfl` 给出。

这里 postcomposition 给出 right action。Scheme action 的复合顺序与 group
乘法相同；直接把它当成 left action 会颠倒顺序。本实现不安装那个错误的实例。
也不要求 action free：椭圆曲线的 automorphisms 可以产生 stabilizers。

## 从一条给定的曲线出发

`YZeroCoarseMarkedComplexCurves` 的输入是真正的
`E : ModularCurves.EllipticCurve (Spec ℂ)`，以及实际 naive full marking α。
`fullMarkingClassifier` 使用同一个 `xFullNaiveRepr.homEquiv.symm`，产生一个
actual fine point；随后 `yZeroComplexSchemePointOfMarking` 使用实际 coarse 投影。

两个 sanity 条件尤其关键：

- `complexFullMarkingNativeIso` 是给定 pointed curve 与 universal pullback 的
  实际 cartesian isomorphism，底映射是 Spec ℂ 的 identity。
- `complexFullMarkingNativeIso_level` 证明 universal full marking 经该同构运输
  后等于输入 α。它由 representability 的自然性和 inverse-bijection law 证明。

因此这不是给每个 j 值随意配上一条不相关的曲线。
`yZeroComplexSchemePointOfMarking_comp_sourceJ` 验证实际 source-j morphism；
`yZeroComplexSourceJValue_of_marking` 将其点值识别为**给定 E** 的 field
Weierstrass model 的 j。

`nonempty_complexFullMarking` 还消除了“假定存在 full marking”的条件：对任意
原生 E 和非零 N，ℂ 上的 torsion-basis theorem 给出 P、Q，且证明在所有
geometric base changes 上仍构成 naive full marking。由此，每个 E 都有 actual
coarse point，其 source-j 等于 E 的 Weierstrass j。classifier 仍要求 `N ≥ 3`，
与上游实际 representability 的范围一致。

反方向，提升任意 coarse point 后，`fullComplexPointEllObj` 与
`fullComplexPointLevel` 给出原生 universal pullback curve 及其实际 marking；
`yZeroComplexSourceJValue_eq_weierstrassModel` 检查其 j 值。

## 原生 marked-curve classes 到实际 coarse points

`YZeroCoarseNativeClasses` 直接使用上游 `GammaHClasses` 的原生定义。其关系允许
一个 pointed same-base `HomOver`，要求 total-space map 是 isomorphism，并要求
它将正向 `glSmul g` 后的两个 sections 送到目标 marking，其中 g 属于 Borel。
这个 quotient 的关系没有重新定义成 classifier 相等。

`gammaHClassesComplexPoint` 已经从给定曲线的实际 classifier 降到这个 quotient。
证明先将 `HomOver.mapPoint` 的正向等式改写成 `EllHom.pullSection` 的等式，再用
classifier naturality 和 positive `glSmul` 公式；实际 Borel fiber theorem 最后
给出 coarse images 相等。`gammaHClassesComplexPoint_mk` 为 `rfl`，其 source-j
公式仍然是给定 E 的 j。

`fullComplexSchemePointOfMarking_native` 验证另一个必要的往返：从实际 fine point
提取原生曲线和 marking 后，再取它们的 classifier，精确得到原 fine point。
因此 `gammaHClassesComplexPoint_surjective` 可以提升任意 coarse point，使用
这个提升的原生曲线/marking 构造原生 class，再由往返等式得到原 coarse point。

从 fine classifier 相等到原生 marked curves 的同构也已有独立接口
`complexFullMarkingIsoOfPointEq`：把两条给定曲线分别识别到对应的 universal
pullback，中间用实际 point equality 识别，再逆向复合第二个同构。
`complexFullMarkingIsoOfPointEq_level` 证明得到的同构确实运输原来的 marking。
`YZeroCoarseEllIsoHomOver` 进一步将这个 EllObj iso 转成实际 `HomOver`：
top map 保持原样，两条 inverse laws 给出 total-space iso，π/zero 相容性来自
原 morphism 的条件。`complexEllHomOfHomOver_complexHomOverOfEllIso` 验证转回
后的 EllHom 就是原 morphism，所以 marking 的 functorial transport 可以直接
改写为原生 class relation 中的 forward `mapPoint` 等式。

单射性已进一步完成。两个原生 representatives 的 coarse images 相同，实际
fiber theorem 给出正向 Borel 元素 g。positive action formula 因此识别
`classify(E, glSmul g α)` 和 `classify(E', β)`。上面的同构与 adapter 将两个
marking 分量变成原关系中的 forward `mapPoint` 等式；配合实际 `IsIso f.hom`
和 g 的 Borel membership，直接由 `Quot.sound` 得到原生 classes 相等。
这里没有预先把 quotient 的关系定义成 coarse-map kernel。

最终接口是：

```lean
gammaHClassesComplexPointEquiv N hN :
  GammaHClasses (Spec (.of ℂ)) N (borel N) ≃ yZeroComplexSchemePoint N hN
```

`gammaHClassesComplexPointEquiv_mk` 的代表元公式是 `rfl`；
`gammaHClassesComplexPointEquiv_symm_of_marking` 恢复给定 E 和 marking 的 class。
`gammaHClassesComplexPointEquiv_sourceJ_mk` 保持给定 E 的 source-j。
`gammaHClassesComplexPointEquiv_symm_of_full` 与 `_symm_of_lift` 更明确地说明：
任何实际 full lift 的原生曲线/marking 都计算出同一个逆像 class。
因此原生 class 已与 lift 的选择无关。此结论仍没有声明任意给定 cyclic
subgroup 的分类，也没有把不同曲线上的 Γ₀ subgroup records 字面设为相等。

247 行保留模块的命名严格编译首次即通过，13 项公理检查都是标准三个公理，
5 个 level-3 sanity 通过，自身零 warning/error。其 source hash 和最终累计
检查记录见 README；独立审阅在 `Cleanup/NativeClassesReview.md`。

## Source j 取遍 ℂ

`ModelGeometricJ` 在任意交换环上为实际 `modelEllipticCurve W` 构造 top
presentation，并验证 base/zero 相容性。因此其 geometric j section 是
`ΓSpecIso.inv(W.j)`。在任意域上，送回系数域后得到原始 W.j。

取实际模型 `modelEllipticCurve (WeierstrassCurve.ofJ z)`，使用上述 marking
存在性和 classifier，就得到 source-j 恰等于 z 的 actual coarse point。
`yZeroComplexSourceJValue_surjective` 和 `yZeroComplexInvariantJValue_surjective`
分别提供 scheme-point 与 algebra-point API，含 level-3 实例检查。
这证明 source-j 的所有复点值，而不是 j 值对 native iso classes 的 injectivity。

`sourceJ_polynomial_eval` 使用实际 C/X pullback 公式，给出 φ(F(j)) = F(φ(j))。
由满射性，多项式关系 F(j)=G(j) 在所有复数上都给出 F(z)=G(z)，于是
`yZeroJPolynomialHom_complex_injective` 证明 ℂ[X]→B 单射。
`yZeroJPolynomialHom_complex_eq_zero_iff` 是对应的 zero-detection API。
这不需要 B 是 domain；也没有声称这个 morphism finite 或证明 B 的 integrality。

## 第一坐标轴与下一条 moduli seam

`ConstantAxis` 已经给出由 full marking 第一 section 定义的 morphism：

```text
constScheme S (ZMod N) → E[N] → E.
```

其 point image 在**每个 test scheme**上形成 AddSubgroup，包括 nonreduced test
schemes。membership 精确等于“通过这个 morphism 分解”，并直接从 E[N] 的
universal property 得到 N-killing。这比只检查 geometric points 更强。

在 affine base `Spec R` 上，坐标轴 embedding 对应 product-ring restriction
`f ↦ (a ↦ f ![a,0])`。它有右逆 `u ↦ (v ↦ u(v 0))`，所以给出 closed immersion。
通过已验证的 `fullLevelIso`，它连接到实际 marked torsion scheme。

已进一步证明 constant projection finite、flat、locally of finite presentation，
其 finrank 在每个 base point 都为 N。因此 `sectionAxisSubgroup` 已打包成原生
`FiniteLocallyFreeSubgroup`；`fullComplexPointAxisSubgroup` 是实际 universal
pullback 上的特化，immersion 等于原来的 axis morphism（`rfl`）。
`HasKillingInt` 直接来自 torsion factorization，没有借用一般的 rank-kills 定理。

`AxisGenerator` 已按以下路线补出原生 divisor-generator 条件：

1. 将 ZMod N 的 label a 对应到 order divisor 的 index `(a-1).val`；
   两个 coefficients 模 N 相同，因此 section 相同，包括 a=0 的 wraparound。
2. 各 constituent section 的 factorization 粘成 constant axis→order divisor。
3. 这是同秩 finite flat schemes 间的 closed immersion，故为 iso。
4. 比较 kernel ideal，得到 bundled subgroup 的 divisor 就是 P 的 order divisor；
   在所有 test schemes 上经 iso 运输 subgroup factorings，证明 `HasExactOrder`。
5. 对 identity fppf cover 使用 exact-order 和 order-divisor 的 base-change 定理，
   得到实际 `IsCyclic`，继而构造实际 `GammaZeroStructure`。

`sectionAxisGammaZeroStructure` 适用于任意 Spec R 上 N 可逆的 full marking；
它不要求 N≥3、不要求 ℂ、不要求 R 或 fine ring 为 domain。
`fullComplexPointGammaZeroStructure` 是原生 universal pullback 上的实际特化，
其 subgroup 和 immersion 与原先的 axis 是 `rfl`。对每个 actual coarse point，
`yZeroComplexSchemePoint_lifts_withGammaZeroStructure` 给出携带这个 Γ₀ datum 的
actual full lift。这个存在性结论并未声称所选 lift 的 datum 与选择无关。
不能仅根据“点像是 cyclic abstract group”就声称上游的 `GammaZeroStructure`：
那个结构还要求 finite locally free subgroup 和其 divisor 的 fppf generator 条件。
旧的 naive→Drinfeld exact-order 引理含 `sorryAx`；本轮的直接构造补齐了这些
条件，所用关键声明的检查均为标准三个公理。retained 模块的累计构建记录见 README。

`BorelAxis` 进一步证明固定 E 上真正嵌入的子群不随 Borel marking 换基改变。
实际 Borel 矩阵的首个对角项是单位 v；`glSmul` 后的第一 section 是正向 vP。
`sectionAxis_zsmul_of_unit` 将新的 axis 写成 constant label scheme 的正向单位
重编号，再复合原 axis。重编号是 scheme iso，因此两个 immersion 的 kernel
ideal 相等。这个证明对任意 scheme 上的 N-killed section 都成立；N 可逆只在
实例化 finite locally free subgroup 时使用。

`sectionAxisSubgroup_glSmul_borel_ker` 的结论是固定曲线内的嵌入子群理想相等，
仍不是包含选定 scheme 和结构证明字段的 `GammaZeroStructure` record 的字面相等。
要下降 quotient-j，还需构造实际商曲线并证明其 j 在对应商曲线同构下相容。
该 leaf 的七项公理检查和三个 sanity 已严格通过，包括模 5 时乘 2、而非乘其
逆单位 3 的 morphism 公式；独立审阅在 `Cleanup/BorelAxisReview.md`。

`SubgroupQuotientGeometry` 已对任意 base scheme 的实际 E/G 证明 quotient projection
flat、surjective，结构映射 universally closed。前两条使用真实 stable affine patches
与 glue cover；后一条通过满射，从原曲线的 proper structure map 下降。公开 wrappers
采用原始 quotient 定义的同一个 chosen killing integer。literal axis 的 killing datum
直接来自 torsion factorization，未借用含 sorry 的一般 rank-kills 定理。

这些是原始 scheme quotient 的性质，还不足以构造 quotient elliptic curve：
下面的新 leaf 已在 locally Noetherian base 上补出 properness，以及 subgroup
projection étale 时的 smoothness。后续也已在locally Noetherian base、
subgroup projection étale下证明smooth relative dimension one；local
Weierstrass presentation仍需进一步证明。
`HopfGaloisLeft` 封装了其局部有限性与 étale 性路线需要的左 B-algebra equivalence；
与上游 coinvariant-algebra equivalence 的底层 ring map 相同，由 `rfl` 检查。

`HopfFinite` 已经用 mathlib 的 faithfully flat descent 证明 chart sections 在
literal coinvariants 上 module-finite。`HopfEtale` 已证明对应的 étale descent，
并用实际 `appLE` 映射把 `Etale G.π` 对齐到 group-ring algebra。这两条通用代数
结论均不要求 domain 或 Noetherian 底环；étale 结论甚至不要求 coefficient algebra
module-finite。几何特化继续使用上游真实 free-patch Hopf–Galois datum。

`SubgroupQuotientChartPullback` 证明真实 target chart 的原像恰为 stable source patch，
并给出 canonical `IsPullback` square。`LocalQuotientGeometry` 把已证明的
coinvariant finite/étale algebra 结果转成真实 local quotient morphism 的性质。
`SubgroupQuotientFinite` 因而通过 target chart cover 证明全局 quotient projection finite；
`SubgroupQuotientEtale` 在明确的 `Etale G.π` 输入下证明全局 quotient projection étale。
`ConstantAxisEtale` 证明 literal axis subgroup 确实满足该输入，未将商投影的 étale
性质作为假设。以上结果均不要求 Noetherian 或 domain 底环。

`QuasiCompact` 保留任意 scheme 的 `QuasiCompact.of_comp_surjective`。
其实际 quotient wrapper 现在直接复用已证明的 universally closed structure map
及 mathlib 的准紧实例。`SubgroupQuotientSeparated` 则通过对角映射的 closed
surjective descent 证明实际 E/G over S separated，通用 lemma 甚至只要求前一个
映射 universally closed 且满射。这些 leaf 已纳入39-module累计严格检查，范围与
receipt见 README。

`LocalQuotientFiniteType` 从实际 E 的 smoothness 得到 source chart finite type，
再对 literal coinvariant subalgebra 使用 Artin–Tate。它同时验证实际 raw quotient
scalar map 与 E 的 `appLE` 相容。`SubgroupQuotientFiniteType` 在真实 source
cover 上使用这条 map，证明 locally Noetherian base 上的 raw quotient locally
finite type、locally finite presentation，并与已证明的 separated/universally
closed 组合得到 proper。这里不需要 subgroup projection étale。

`HopfSmooth` 使用 clean étale faithfully-flat algebra descent，
`SubgroupQuotientSmooth` 再沿同一个真实 source cover 粘合，证明 locally
Noetherian base 上且 subgroup projection étale 时的实际 structure map smooth。
literal axis 满足该 étale 输入。`KaehlerRank` 和 `StandardSmoothRank` 分别提供
étale base change 的 Ω 局部秩比较，以及 standard relative dimension 的 rank
接口；`LocallyStandardSmoothRank` 已进一步将 actual locally-standard cover
转成每个 prime 的秩结论。新增 `SmoothRankCriterion` 给出 smooth algebra 常恒秩
与局部 standard relative dimension 的等价；actual source-chart rank1 经真正
faithfully-flat étale inclusion 下降到 coinvariants，再沿 actual base-algebra
同构传给 raw quotientBaseHom。`SubgroupQuotientRelativeDimension` 使用原来的
source cover 和 structural triangles，证明 locally Noetherian base 和 subgroup
étale 下 raw/public/axis quotient 的 smooth relative dimension1。这些新 rank / dimension
模块已分别严格具名检查及独立审阅，并纳入60-module累计gate。

`SubgroupQuotientIntegral` 对任意域上的实际 E/G 证明 integral：原 E 的 integrality
来自已独立检查的 native field theorem，商的 reducedness 经 faithfully flat local
stalk map 的单射下降，irreducibility 经 continuous surjective image 下降。
它不要求 Noetherian、étale 或代数闭，也没有假定商的 elliptic model。
这里的 E/G integrality 不能用来断言 full-level 或 actual coarse moduli scheme integral。
以上截至 integral 的八份 geometric/rank 模块已纳入47-module累计检查，共418项公理 checks、77个 examples，
该47-module历史checkpoint已保留。最终135-module gate覆盖后续relative dimension、
function-field、native field-model、rank/constants/stalk、源genus、整闭性及place/divisor模块，
共1263checks/258examples/9599jobs；范围和逐模块源码哈希见README、current receipt
与独立Cumulative135Verification。历史99/126检查单独保留。

`FiniteFunctionField` 用 literal affine germs 和 fraction-ring base change 得到实际
native function-field finite extension；实际 quotient raw/public/axis 特化亦已通过。
`FunctionFieldFormallyUnramified` 和 `FunctionFieldEtale` 再与真实 étale quotient
projection 组合，给出任意域上 actual native field pullback étale。它们不引入额外
scalar tower 或 quotient model，且泛型 field étale 不等于 places 无分歧。这些新增
function-field 模块已纳入60-module checkpoint和历史99-module累计gate。

新增的实际quotient rank/degree比较证明 native E→E/G 函数域次数等于subgroup rank，
真实 étale projection在每个点的stalkMap扩张最大理想等式也已验证。native E的
函数域与Weierstrass函数域具有保持独立几何常数的AlgEquiv，实际chosen coordinate
ring是native函数域的分式环。实际源 E 的完整RatFunc/finite/separable pack、满常数域
及intrinsic genus=1也已纳入99-module gate。raw商的独立几何κQ-compatible AlgHom、
满常数域、超越元素存在性、全部stalk和非空affine截面整闭亦已检查。

通用闭点DVR、实际stalk标量塔、canonical stalk/function-field交换图，以及intrinsic
Place与DVR adic valuation的字面一致性均已验证。实际étale商的stalk长度定义指数=1，
后续已将它与所有source intrinsic places的normalized valuation相等连接；
全局Riemann–Hurwitz公式仍需证明。
尚无raw E/G genus、quotient Weierstrass model或target-j/Φ relation。

99-module checkpoint之后，闭点DVR place的normalized valuation已与真实FU+LFT
映射连接，并给出实际raw/public étale商的兼容公式。proper valuative lift、有限
residue闭中心、真实中心stalk交换方块，以及DVR image恢复place均已分别检查。
原生椭圆曲线全部places的有限residue及闭点表示已有无额外输入的接口。
特征零实际商亦已证明全部places的有限residue，étale subgroup时已有闭点表示。
separated integral smooth curve上的closedPointPlace单射也已证明：真正valuative
uniqueness比较带相同generic/base triangles的两个canonical lifts，再比较实际中心。

商自身参数的有限性及scalar tower亦已检查，而旧source x下降的rank-divides-2
障碍已经正式证明。新参数避免这个真实障碍；特征零商已有finite/separable pack，
原始几何常数及所有towers都已正式检查。跨域genus比较仍未建立。
这些新增27个模块均已纳入126-module累计检查，历史99-module记录保留不变。

126之后的九个新增模块进一步完成闭点/place双射包装、主除子valuation、
实际place map及有限纤维、通用/实际加性除子拉回和主除子兼容。每个模块均已
严格具名编译及独立源码/输出审阅，现已全部纳入最终135-module累计检查及独立audit。

商的 elliptic model 还需要 genus-one 或直接模型构造。上游 cotangent H¹ descent
中的 H¹ 是 cotangent complex 的 H¹，不能充当曲线的 H¹(𝒪) 或 genus 证明。

## API 的分工和取舍

| 层 | 适合的用途 | 限制 |
| --- | --- | --- |
| invariant-ring algebra points | 计算 global sections、源 j、检测等式 | scalar algebra 必须是实际 structure map 给出的那个；本轮已检查 alignment |
| actual scheme points | 与原生曲线、cartesian pullbacks、coarse 投影连接 | affine Spec/Γ 的 plumbing 较多，已封装双向 equivalence |
| actual Borel orbit quotient | 精确描述 coarse projection 的复点纤维，保留 stabilizers | 这是集合层的 equivalence，没有声称 analytification 或 scheme quotient 的额外同构 |
| native marked curves | 从给定 E、P、Q 出发，检查实际 marking 与 j 的运输 | 仍需将 Borel orbits 与给定 cyclic subgroup 的 moduli datum 联系 |
| actual native GammaHClasses | 直接使用原生等价关系，与 actual coarse 复点双向转换；可用任意 full lift 计算逆像 | 集合层的 moduli classification；未证明任意 Γ₀ subgroup datum 的全分类，也未给出 quotient-j |
| independent plane model | 使用本地 Φ、最小多项式和 modular-function field 结果 | 尚未得到 actual `YZeroCoarse → planeScheme` 的第二坐标 |

这些 API 把可验证的实际 moduli 输入暴露出来。剩余关键问题是构造 E/C 的 elliptic
curve 与 regular quotient-j，证明实际 isogeny/lattice compatibility，再证明 Φ
vanishes。finite birational、normality 和 normalization 也仍需独立证明。点商双射
和 source-j 兼容性不会自动给出这些结论。
