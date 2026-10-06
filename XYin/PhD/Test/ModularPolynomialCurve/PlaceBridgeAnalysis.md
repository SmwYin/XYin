# 实际 subgroup quotient 的函数域与 places：接口分析

这里的 Q 始终指原生椭圆曲线 E 的实际 scheme quotient E/G。
Q 与 coarse moduli scheme `YZeroCoarse` 是不同对象；前者的几何性质
不能直接移用于后者。所有底域标量来自各自 structure map 和 generic germ。

## 新参数解决什么问题

原生 E 的 Weierstrass x 给出 `[K(E):k(x)]=2`。如果同一个 x 经真正标量塔
下降到 Q，而 `[K(E):K(Q)]` 等于 subgroup rank r，则 r 必须整除2。
`NativeCoordinateTowerObstruction` 已正式证明这个条件结论及 rank3 矛盾。
因此一般商不能直接复用源 x；这不是常数标量的问题，而是非不变坐标的问题。

实际 K(Q) 已证明存在超越元素。任意这样的 t 给出
`RatFunc.algHomOfTranscendental t ht : k⟮X⟯ →ₐ[k] K(Q)`，保持原常数，
X 映为 t，多项式限制就是 aeval t。商域嵌入真正 K(E) 后，源函数域的
有限性证明新参数的有限性，无须假定该参数或旧 x 可以从源下降。
`YZeroCoarseSubgroupQuotientParameterFunctionField` 提供具体的三条 scalar
towers 和 FunctionField 结构，调用者可以分别安装所需实例。

任意域的版本已证明有限性；特征零版本另给出可分性。后者覆盖 ℂ，API
没有要求调用者另提供 separating chart。正特征中，任意超越参数可能
不是分离参数，例如 t=s^p；不能把当前可分性结论直接改成 PerfectField k。
这些临时 chart scalars 是证明工具，places 的最终陈述仅暴露原始几何常数。

## 几何 points 与 intrinsic places 的桥梁

| 接口 | 最小已验证范围 | 提供的效果 |
| --- | --- | --- |
| `closedPointPlace` | integral X，smooth relative dimension1，实际闭点 | literal stalk DVR 定义原生函数域的 intrinsic place，membership 等于真实 stalk 像 |
| `stalkClosedPointTo_comp_functionField` | irreducible X，真实 generic lift | 从实际 Spec 方块推出中心 stalk 与 generic stalk 的交换式；不假定 ring square |
| `closedPointPlace_eq_of_generic_lift` | integral smooth curve，真实 generic lift 的中心闭 | 从实际 stalk 像恢复原 place；不要求 proper |
| `exists_closedPointPlace_eq` | proper integral smooth curve，place residue 有限 | 给出真正闭点表示；residue 有限性在通用接口中明确保留 |
| `nativeField_exists_closedPointPlace` | 任意域上的原生椭圆曲线 | 自动证明 residue 有限性，所有 source places 都有闭点表示 |
| `gluedQuotient_exists_closedPointPlace` | 特征零，实际 subgroup étale | 实际商域所有 places 都有闭点表示，无外加 chart 或 residue 输入 |
| `closedPointPlaceLift` | integral smooth curve，实际闭点 | 构造正向 Spec lift，证明 generic/base triangles 及中心等于原闭点 |
| `closedPointPlace_injective` | integral smooth curve，separated structure map | 相同 place 强制闭点相同；通过真正 valuative uniqueness，无需 proper 或 residue 输入 |
| `closedPointPlaceEquiv` | proper integral smooth curve，所有place residue有限 | 将真实闭点构造包装成双射，正向字面等于closedPointPlace；native E任意底域自动供给所有输入 |
| `gluedQuotientClosedPointPlaceEquiv` | CharZero，实际subgroup étale | raw/public Q的真实闭点与intrinsic places双射；无model/genus/外加chart输入 |

这些模块构造并验证实际对象，未把所需中心、交换式或点对应藏进 record 假设。
通用接口较长，原因是它显式保留独立常数及实际 stalk algebra；native E 和
raw/public Q wrappers 将必要几何实例从已证性质安装，调用时不必重复 plumbing。

## 无分歧结论的准确边界

`YZeroCoarseSubgroupQuotientPlaceRestriction` 适用于任意域，只要求实际
subgroup étale。对每个 source intrinsic place v，它给出实际商域 place w，
满足所有 z 上 `w.valuation z = v.valuation (q.functionFieldMap.hom z)`。
证明由 source 闭点表示、finite q 的闭点像以及已证 normalized stalk
valuation 公式组成。因此输入中没有闭点表示、residue、chart 或 CharZero 假设。

`gluedQuotientPlaceMap` / `quotientPlaceMap` 已将该存在性包装成实际place map。
通用 `Place.valuation_injective` 从真实valuation-subring恢复式证明归一化valuation
决定place，因此选择所得map有字面valuation公式，且闭点place的像等于实际q(x)的place。
这一步也适用于任意底域，不依赖CharZero或target全体place的闭点表示。
有限纤维已由实际source闭点表示、target闭点place单射性及
`Scheme.Hom.finite_preimage_singleton` 正式证明；此处无需CharZero或target所有places表示。
`FinsuppFiniteFiberPullback` 给出允许多对一的有限支撑加性拉回，实际raw/public商
wrapper的系数就是 `D (r v)`。`Finsupp.comapDomain` 要求相关部分单射，
不能用于一般多对一商映射。
`PrincipalDivisorValuation` 已验证主除子系数的归一化valuation公式：
`v.valuation u = WithZero.exp (-(principalDivisor u v))`。当前native principal-map
依赖明确的finite/separating chart scalars，定理保留这些输入，不要求满常数域或genus。
`PrincipalDivisorPullback` 已用真实map公式、exp单射性和有限纤维正式证明
跨域主除子兼容。实际raw/public商wrapper在CharZero+Etale Gπ下，使用Q自己的
超越参数和从真实几何推出的finite/separable/tower pack，得到
`q* (div u) = div (Units.map q.functionFieldMap.hom u)`。
通用版保留两套chart及valuation输入，实际版无需调用者另交chart、genus或model。

主除子拉回已经完成；canonical divisor/differential 比较及加权 degree
拉回也是新的证明任务。已有的单域 Riemann–Roch 或 polar-degree bound
不等于跨域 Riemann–Hurwitz。Q 的 genus=1、Weierstrass model、实际 target-j、
Φ relation 与最终 coarse/plane normalization 比较目前仍未证明。

## 验证范围

本页列出的接口均已有逐文件正确模块名的严格编译、完整公理检查和实际 API
示例；具体 session、源码及产物哈希见 `Cleanup/` companions。
历史99-module checkpoint保留不动；126-module fresh累计检查与独立audit均已通过：
9590 jobs、1171项逐条公理输出、240个实际API examples、756项canonical artifacts，
源码、清单、strict设置与编译前冻结记录一致。完整边界和provenance见
`Cleanup/Cumulative126Verification.md`；该检查不证明本页明确列出的未完成数学结论。

126之后的九个新增模块各自经过正确模块名的严格检查及root实际源码/完整输出/产物
审阅，现均纳入最终135-module fresh检查及独立audit：9599jobs、1263项精确公理输出、
258个API examples、810项canonical artifacts。原126份源码保持byte-exact；
最新来源及验证边界见`Cleanup/Cumulative135Verification.md`。
