# MMeromorphic、modular functions 与实际 YZeroCoarse：结果和继续入口

这份文档区分已证明的定义/field 比较、独立模多项式模型，以及实际 AINTLIB
moduli 对象。最终的实际 `YZeroCoarse` 与模多项式曲线 normalization 的识别
尚未完成，不能把下面的中间桥梁当作该结论。

## Meromorphy predicate 的选择

| 版本 | 已验证范围与用途 | 取舍 |
| --- | --- | --- |
| 上半平面 wrapper | 直接对 `f : ℍ → ℂ` 陈述，封装坐标定义，提供加乘逆和全纯复合 | 满足 modular-function 实验需求，范围局限于 ℍ |
| preferred-chart predicate | 一维复 C¹ 流形，compatible charts 下坐标无关；包含通常的 Riemann surfaces | 最容易接现有 `MeromorphicAt`；isolated poles 的定义不能直接替换成高维模型 |
| 局部解析分式 | boundaryless 复解析流形上的 scalar functions，允许任意复赋范模型；无有限维/模型完备性假设 | 推荐的通用直接 predicate；一般全纯 pullback 在高维失败，已提供开放解析映射的 pullback |
| sheaf localization | regular germs 的 localization 再 sheafification，符合 Stacks 01X1 | 可以覆盖更大的 locally ringed spaces；点值 predicate 不表示一般 nilpotent sections，field 也需另外证明 |

局部分式要求分母的非零 locus 在整个邻域中稠密，并只在该 locus 比较
`f=a/b`。它不要求分母在 pole 处非零，也不限制 exceptional point values。
基本算术、一般解析流形的 inverse、一维 chart/fraction 比较和 ℍ 特化均有
Lean 定理。`MMeromorphicOn` 当前是 ambient-neighborhood notion，对任意 thin
subset 不声称是 within notion。更大的 analytic-space/LRS 版本需要自己的
structure sheaf 和 equality，不能机械沿用一变量的 codiscrete exceptions。

使用 `MDifferentiable` 的接口优势确实是对原函数陈述并统一流形复合。
但是坐标形式的加乘并不困难：`DifferentiableOn.add/mul` 与预复合在这里
definitionally compatible，独立测试已验证。不能从实现推断历史作者的动机。

## Field 条件在 predicate 之后证明

原始函数 subtype 不能配 pointwise field：singular point 的任意赋值造成
零因子，pointwise reciprocal 在零点不满足逆律。测试包含这两个反例。
已经实际构造并比较三种一变量版本：

1. 忽略 codiscrete exceptions 的 meromorphic classes；
2. 唯一 normal representatives，运算后 normalize；
3. 参考 meromorphic sheaf 的 sections。

非空连通复开域上的 field 以及 classes/NF/sheaf 的 `RingEquiv` 均已证明。
任意复开域的 quotient/sheaf ring comparison 也已证明，未把 global sections
假设为 global quotients。解析条件先独立定义，随后才把满足条件的函数送入
field；没有把 modular-function condition 定义成 field membership。

classes 适合代数和映射；NF 适合唯一代表和求值，但加乘必须 normalize。
NF 的 coercion 不能无条件保持 raw pointwise 加乘，pole cancellation 后的
evaluation 也不是到 ℂ 的 ring hom。一般高维 field 比较尚未正式建立。

完整定义、API、反例、最小假设和文件分工见
[MMeromorphic/README.md](MMeromorphic/README.md)。

## 指定的 cusp condition 与 level one

production `ModularFunction` 已使用独立 manifold NF predicate，并把 cusp
字段改成 `c.IsExpBoundedAt toFun 0`。其定义正是

```lean
∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsOfExponentialGrowth (f ∣[k] g)
```

与通常 q-meromorphic cusp condition 的 iff 是另行证明的，允许有限阶 pole。
指定 chart 版使用 NF、正 period 和 periodicity；all-cusp 版从 discrete
slash-invariant group 的 cusp stabilizer 取得正 period。Raw 版明确保留 eventual
holomorphy，不能从允许任意 exceptional values 的 raw predicate 无条件推出
exact q-germ。`SL₂(ℤ)` 满足所需群假设。

本地已有实际 `RatFunc ℂ ≃ₐ[ℂ] ModularFunction SL₂(ℤ)`；独立构造的
`Proj ℂ[X₀,X₁]` 的真实 scheme function field 也已与它同构，几何 ratio
coordinate 映到 j。这完成标准 projective j-line 模型的函数域比较。
它尚未识别一个独立 compact analytic X(1) 或 AINTLIB compactification。

固定版本的源码审计没有找到完成的具体 X(1) 或 X₀(N) 紧化。实际 `YZeroCoarse`
存在；辅助 level 的 `YHCoarse` 商也提供 Y(1) 的构造路线，不应因 full-level
cover 要求 N≥3 就断言不存在 level-one 路线。详情见
[MMeromorphic/AINTLIBSourceAudit.md](MMeromorphic/AINTLIBSourceAudit.md)。

## 模多项式与实际 YZeroCoarse

本地六个模块已独立构造
`Spec (ℂ[X][Y]/(Φ_N))`，证明 integral 性、evaluation kernel、真实复 scheme
points 与 Γ₀(N) orbit map 的满射，以及其 scheme function field 与
Γ₀(N) modular-function field 的 ℂ-algebra 同构。

正确的最终曲线目标一般是 normalization，不能把平面模型直接当成 Y₀(N)。
N=2 的 CM node 是分支丢失的具体例子。函数域同构本身不能确定开放曲线的
所有点或指定 scheme 的同构。

实际 AINTLIB 分支已经完成 source-j 的 regular construction/Borel descent、
真实 coarse/fine 复点的 lifting/orbit comparison、实际原生 marked curves 和
cyclic axis datum。随后针对真正的 subgroup quotient `Q=E/G` 建立了：

- integral/proper/smooth-relative-one 的适用版本，真实 finite étale projection、
  原常数上的函数域 AlgHom、degree=subgroup rank、满常数域及自己的有限参数；
- source/native 和 characteristic-zero Q 的全体 places 的有限 residue，真实
  closed-point/Place 双射；通用版的 residue 假设明确保留；
- 任意底域上实际 étale 商的 place map、normalized valuation 公式及有限纤维；
- 容许多对一映射的 finite-support additive pullback、实际raw/public商的除子
  拉回，以及CharZero下真实函数域拉回与主除子的兼容定理。

这些构造保留 E 和 Q 各自 structure map 定义的原始常数。一般商不能直接复用
source x：真实 scalar tower 若使旧 x 下降，会迫使 subgroup rank 整除2；
rank3 矛盾已正式证明。Q 自己的超越参数避免这一障碍。特征零保证该参数
可分；正特征中任意超越参数可为 p 次幂，不能直接把声明改成 PerfectField。

Q 是某张椭圆曲线的商，与 coarse moduli scheme `YZeroCoarse` 是不同对象。
Q 的 integral/normal 性不能被用于断言 coarse moduli scheme integral/normal。

## 剩余的实质数学

当前尚未证明 Q 的 genus=1、Weierstrass model、相对/functorial target-j、实际
cyclic-isogeny 与 lattice inclusion 的兼容性，以及最后的 Φ identity 和
finite birational/normalization comparison。已有 source-j、复点商双射和
place/divisor 局部公式都不能替代这些步骤。

上游 `quotientCurve` 仍消费缺失的 local Weierstrass theorem。另一条已证明的
free-base-action family descent 要求 zero equivariance，不能用于非零 subgroup
translation。单域 Riemann–Roch 也不提供跨域 Riemann–Hurwitz：还缺 canonical
divisor/differential 比较及 weighted degree 拉回。不能给这些结论套一个含有
目标结论的 record 假设来宣称完成。

具体未完成定理和源码依据见
[ModularPolynomialCurve/YZeroCoarseComparisonGaps.md](ModularPolynomialCurve/YZeroCoarseComparisonGaps.md)。
各版本的 place/parameter API、假设和取舍见
[ModularPolynomialCurve/PlaceBridgeAnalysis.md](ModularPolynomialCurve/PlaceBridgeAnalysis.md)。

## 环境与可复现检查

MMeromorphic 和本地 plane-model 测试使用 XYin 原有 Lean 4.30；AINTLIBDrafts
使用独立 pinned Lean 4.35.0-rc3 环境。没有升级主项目或修改原生依赖证明。
两个版本不能混合导入。正确入口和 exact revisions 见各目录 README。

历史126-module fresh检查及独立审计已保存：9590jobs、1171项精确公理输出、
240个实际examples、756项canonical artifacts。原有源码保持byte-exact。
最终135-module fresh检查及独立audit已通过：9599jobs、1263项精确公理输出、
258个实际examples、810项canonical artifacts、零自身诊断和sorryAx。
全部旧126份源码保持byte-exact；新增九份逐个经过正确模块名的strict编译、
完整公理输出、实际API与数学源码审阅。历史记录单独保存。
最终记录见[ModularPolynomialCurve/Cleanup/Cumulative135Verification.md](ModularPolynomialCurve/Cleanup/Cumulative135Verification.md)。
最新验证记录以 [ModularPolynomialCurve/README.md](ModularPolynomialCurve/README.md)
和相应 `Cleanup/`/`Checkpoints/` 文件为准。没有把未通过的临时尝试计入成功记录。

本轮已使用用户许可的唯一一次reset；没有再reset或使用credit。为遵守额度约束，
最终检查点保存后停止全部证明和编译工作。继续入口是实际商的主除子拉回，
下一步需建立加权degree和canonical/differential比较，再处理genus/model；
最终实际YZeroCoarse识别仍未完成。
