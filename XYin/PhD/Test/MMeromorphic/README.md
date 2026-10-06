# MMeromorphic：独立定义、一般性与 field 的实验

## 建议与已验证的范围

最终的通用设计建议采用 **局部全纯分式**，以 `MMeromorphicAt I f x`、
`MMeromorphicOn I f s`、`MMeromorphic I f` 提供直接作用于原始函数的接口。
普通复解析流形足以覆盖上半平面，又可以推广到高维乃至无限维复赋范模型。
一维 preferred-chart 版本应保留为与现有 `MeromorphicAt` 对接的简单刻画。
最初的独立设计保留在实验命名空间中。本次 cusp 条件跟进另外修改了 production 的
modular-function 定义，见文末新增说明；没有修改 mathlib。

最初独立设计轮没有读取 `XYin/PhD/ModularFunctions` 的内容。设计先独立提出，再对照
mathlib、指定 Zulip 讨论和其中的外部 sheaf 实现验证。

| 文件 | 定义/目的 | 已证明的主要结果 | 主要取舍 |
| --- | --- | --- | --- |
| `UpperHalfPlane.lean` | 最小上半平面 predicate | MDiff 蕴涵、算术、逆、全纯复合、正行列式群作用 | 容易接 modular forms，但限定 ℍ |
| `Charts.lean` | 复直线模型上的 preferred-chart predicate | chart independence、算术、全纯复合；向量值也适用 | 坐标兼容只需复 C¹；仅一维 |
| `LocalFraction.lean` | 任意复模型上的局部解析分式 | 算术、开放解析 pullback、局部解析坐标变换；一般解析流形上的逆 | scalar-valued；高维一般 pullback 不成立 |
| `Comparison.lean` | 局部分式与 chart predicate 的比较 | 一维解析复流形上 At/On/global 的 chart ↔ fraction 等价 | 通过下一文件进一步取得 C¹ corollaries |
| `RiemannSurface.lean` | 一维 C¹→解析的 named theorem | C¹ Riemann surfaces 上 LF↔Charts、inverse、MDiff implication 与 pullback | 没有新增自动全局 instance，也未泛化到任意 incomplete 模型 |
| `Field.lean` | 先由 predicate 构造 classes，再证明 field | 连通域上 classes 的 Field；normal forms 的 Field；二者 `RingEquiv` | 这里的 codiscrete quotient 是一变量构造 |
| `ModularField.lean` | 内部 meromorphy、weight-zero invariance、cusp q-meromorphy | 原始条件的闭合性，以及所得 classes 的 `Subfield`/`Field` | cusp 坐标族是显式输入，未替特定 Γ 枚举 cusps |
| `ModularSlashChecks.lean` | 与 mathlib bundled modular API 对接 | determinant-one 下 ordinary invariance ↔ slash invariance；`toSlashInvariantForm` | 仅 positive determinant 不足以去掉当前 slash 的因子 |
| `Reference/`、`SheafChecks.lean` | 对照外部 locally ringed space sheaf 实现 | 一般 sheaf field criterion；复平面上的实际 field | 参考代码移植，尚未泛化为所有复流形上的 holomorphic LRS |
| `SheafLocalBridge.lean` | 从直接解析条件进入参考 sheaf | `MeromorphicAt ↔ Nonempty LocalSheafFraction`；localization→sheafification | field 同构需要后续 global comparison |
| `SheafGlobalBridge.lean` | 从直接 predicate 全局粘合 | overlap 的分式相等、unique gluing、`MeromorphicOn f univ → meromorphicGlobalSections` | 正向构造，反向需局部 lifting 与 normal gluing |
| `SheafOpenBridge.lean` | 任意开域上的直接 sheaf construction | 局部分式 restriction、任意开域 gluing、UHP condition→上半平面 sheaf section | 不把开域 section ring 与另一个 LRS 的 global sections 当作定义相同 |
| `SheafOpenField.lean` | 一般 connected open 上的 section field theorem | nontrivial、zero-or-unit meromorphic stalks 蕴涵 connected open sections 是 field；上半平面实例 | 证明 field 所需的全局假设与 predicate 定义分离 |
| `SheafArithmeticBridge.lean`、`SheafQuotientBridge.lean`、`SheafOpenQuotientBridge.lean` | 两个独立构造的正向 comparison | 任意复开集上 classes→sheaf 的实际 RingHom，保持加乘与 1 | 不依赖 field structure |
| `SheafFractionEquality.lean`、`SheafOpenInjective.lean` | comparison 的 equality | sheaf equality ↔ codiscrete equality；任意复开集上 injectivity | 包括空集与不连通域 |
| `SheafReverseBridge.lean`、`SheafLiftData.lean`、`NormalGluing.lean`、`SheafSurjective.lean` | 从 sheaf section 恢复 analytic representative | 局部分式 lift、punctured compatibility、NF 粘合、恢复原 section | 没有假设全局 section 是全局 quotient |
| `SheafEquivalence.lean` | 完整的构造比较 | 任意复开集上 quotient↔sheaf `RingEquiv`；connected nonempty 上 NF↔sheaf `RingEquiv` | 一维复开集比较，未声称适用于所有 LRS |
| 各 `*Checks.lean`、`IntegrationChecks.lean` | 证明调用方式和排除错误设计 | 算术/复合 API、多个反例、predicate→field、不同版本的桥接 | 都是编译过的定理与例子，未以公理代替分析结论 |

## 为什么用 MDifferentiable：用户原判断的核实

mathlib 的 `ModularForm.holo'` 确实直接写 `MDiff f`，而上半平面的
`mdifferentiable_iff` 把它改写成
`DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im}`。
这能够说明直接接口的作用，不能单凭实现推断当年作者选择它的历史动机。

“后者关于 f ∘ ofComplex 而非 f”是准确的。但“后者做 addition/multiplication 不方便”
需要收窄：已有 `DifferentiableOn.add/mul`，以下例子不需要 `simp`，直接编译通过：

```lean
example (hf : DifferentiableOn ℂ (f ∘ ofComplex) U)
    (hg : DifferentiableOn ℂ (g ∘ ofComplex) U) :
    DifferentiableOn ℂ ((f + g * f) ∘ ofComplex) U :=
  hf.add (hg.mul hf)
```

加乘与预复合在这里 definitionally compatible。真实的摩擦主要在流形间 composition、
坐标域/coercion/extension 和 `MapsTo` 的处理，以及让其他 API 总是对原函数 f 陈述。
因此建议是“隐藏坐标实现、提供原函数 API”，不是“坐标版缺少算术定理”。

## 版本 1：只服务 modular functions 的最小定义

`UHP.Meromorphic f` 定义为

```lean
MeromorphicOn (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}
```

定义内部仍用坐标，但外部的 type 是 `f : ℍ → ℂ`，无需每次重写函数。
`of_mdifferentiable`、`add/mul/inv/div/pow`、`comp hf hh`、`comp_smul` 均已证明。
这是足够实用的实验方案，不必先建立 sheaf 或 field。
普通加乘并不需要新的数学；composition 的坐标转换集中在一次封装证明中。

## 版本 2：一维流形上的 chart predicate

```lean
def MMeromorphicAt (f : M → E) (x : M) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
```

定义仅需要 `[TopologicalSpace M] [ChartedSpace ℂ M]`；要使它具有坐标无关的几何含义，
使用 `[IsManifold 𝓘(ℂ) 1 M]`。已证明任意 compatible maximal-atlas chart 都给出相同判定。
因为复 C¹ transition 在一维是 analytic，不需要把定义先限制在 Cω manifolds。
这个接口包含通常的 Riemann surfaces；本地定理不必额外要求 Hausdorff、second countability、
connectedness。若要使用这些词的传统几何定义，可另加相应全局假设。

向量值 `f : M → E` 可用；已有 add/neg/sub 与复标量 smul，mul/inv/div API 当前限于 scalar ℂ。
MDifferentiable→meromorphic 的 Banach-valued theorem 要求 `CompleteSpace E`。
例如 API checks 的 `(hf.add hg).div hh` 和 `hf.comp_mdifferentiable hg` 都直接作用于原函数。
在 ℍ 上 preferred chart 恰好是 `ofComplex`，At 比较甚至是 `Iff.rfl`。

缺点是现有 `MeromorphicAt` 表示的是一变量 isolated-pole 性质，不能把模型 ℂ
机械替换成 ℂⁿ。`z₁/z₂` 的 exceptional set 是 hypersurface，要求 codiscrete 已经不合适。

## 版本 3：推荐的局部解析分式

当前 scalar-valued 定义的内容是：存在包含 x 的开集 U 和 `a b : M → ℂ`，使得

1. a、b 在 U 上 `ContMDiffOn I 𝓘(ℂ) ω`；
2. `U ⊆ closure (U ∩ {y | b y ≠ 0})`；
3. 在 `U ∩ {y | b y ≠ 0}` 上 `f y = a y / b y`。

第二条命名为 `RegularDenominator`，要求非零 locus 在整个 U 中稠密。
不能只要求“b 在某点非零”，因为 U 可能不连通，另一分支上 b 可以恒零；
不能要求 `b x ≠ 0`，否则排除了真正的 pole。
第三条有意不约束分母零集上的 point values，符合现有 `MeromorphicAt` 的 convention。
这也允许 numerator=0 的情况；它并不把“恒零”和“所有代表值恒零”混为一谈。

定义和基本算术在任意 `ModelWithCorners ℂ E H` 上可陈述，所需 typeclasses 很少。
本轮证明的几何 inversion 范围则明确是
`[ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]` 的 boundaryless 解析复流形。
没有使用 `[FiniteDimensional ℂ E]` 或 `[CompleteSpace E]`。
这是经过任意 normed complex model 的检查得出的更大一般性，并非只测试了 ℂ²。
不要把“定义可以陈述于任意 I”误报成“已经证明任意 corners 模型上的几何 inversion”。

逆的证明在一个 connected ball 上用 analytic identity principle：numerator 的 germ
要么为零，要么其非零 locus 稠密。交换 numerator/denominator 时还要保留旧分母来
忽略旧 exceptional values；实现使用 `b*b/(a*b)`，不是未经检查的 `b/a` 全点等式。
这个细节使一般维数的逆真正成立。

在 ℂ 上它与 mathlib `MeromorphicAt` 完全等价；在 ℍ 上与最小 UHP condition 完全等价；
在一般一维 analytic manifold 上与 preferred-chart At/On/global predicates 完全等价。
`RiemannSurface.lean` 还提供一维 `IsManifold 𝓘(ℂ) 1 M → IsManifold 𝓘(ℂ) ω M`
的 named theorem，进而让上述比较与 inverse API 只要求通常的复 C¹ compatibility。
同一文件还提供 C¹ 一维流形上的 MDifferentiable implication 与任意 MDifferentiable pullback。
这不新增全局自动 instance，也不要求用户自行补出解析兼容性的证明。
因此 modular functions 可以最终采用这个通用定义，同时用一维 API 减少使用时的坐标转换。
这里没有声称或测量 Lean elaboration/runtime 的性能优势。

`MMeromorphicOn` 当前是“每个 s 中点在 ambient manifold 的一个邻域 meromorphic”，
不是沿 thin subset 的 within notion。这一点与 `MDifferentiableOn` 的一般 set 语义不同；
对 modular functions 的整个 ℍ 不造成问题。推广边界/任意非开 s 前需要另行选定语义。

## Composition 的一般性存在真实边界

一维代表函数版允许任意 holomorphic map，甚至 constant map 到所赋 pole value。
但这并不表示它在 classes 或 sheaves 上也诱导 pullback。
`FieldChecks.constant_pullback_does_not_preserve_zero_class` 已证明：只在 0 为 1 的 spike
代表 zero class，预复合常值 0 后却代表 one class。

高维连代表函数版的一般 holomorphic composition 都失败，Checks 给出反例：

```text
f(z₁,z₂) = if z₂ = 0 then conjugate(z₁) else 0
h(z) = (z,0)
```

f 满足局部分式条件，用 0/z₂ 表示；h 全纯；f∘h=conjugation，不 meromorphic。
所以应提供带 denominator-preservation 条件的 pullback theorem。
本轮已经证明开放解析映射 `comp_open` 与局部解析 partial homeomorphisms 的版本。
开放是充分条件，不宣称必要；泛化到合适的 dominant maps 应放在相应几何 setting 中。
模群的正行列式作用是 biholomorphic，不受这个障碍影响。

## Field：为什么必须在 predicate 之后改变 equality 或 operations

不能给原始函数 subtype 配 pointwise field。两个独立检查排除了它：

- spike 与非零 holomorphic function 的乘积可处处为零，产生零因子；
- 上半平面上的 `f(τ)=τ-I` 非零，但在 τ=I 处 `f*f⁻¹=0≠1`。

因此“predicate 对 inv 闭合”只证明了 analytic 闭合性，不是 field inverse law。
field 中相等必须忽略无意义的 singular point values，或选择唯一 normal representative
并改变运算。这不是把 analytic condition 定义成 field membership。

`Field.lean` 先用已独立定义的 `MeromorphicOn` 选出
`Filter.Germ (codiscreteWithin U) 𝕜` 中的代表 classes，再由 identity principle 证明：
在 `[NeBot (codiscreteWithin U)]` 且 `IsPreconnected U` 时，这个 ring 是 field。
scalar field 甚至可以是任意 `NontriviallyNormedField 𝕜`。
非空开 U 自动满足所需 `NeBot`；空域不能产生 nontrivial field。
这里的 `Filter.Germ` 是忽略 codiscrete exceptions 的 quotient，**不是** sheaf 在一点的 stalk。

在相同的非退化 connected-open 假设下，另一个实际验证的 field 是
`NormalMeromorphic U`：采用 mathlib `MeromorphicNFOn`
的唯一 normal representative。它与上述 classes 有 `normalRingEquiv`。
加乘与逆经 transport 定义，已证明等于对应 raw 运算后再 normalize。
不能只把 raw predicate 改成 NF 然后保留所有 pointwise operations：
`1/z` 与 `(z-1)/z` 都是 NF，raw sum 在 0 等于 0，在别处等于 1，故 sum 不是 NF；
其 normalization 才是常值 1。该反例及 normalize 结果均有证明。

使用上，classes 版本最适合 algebra 与 maps；NF 版本最适合需要 canonical pointwise
representative 的求值、局部阶数等操作。两者是等价表达，不能误认为两套不同数学对象。
这里也有与 `ModularForm` 的 bundled-function API 不同之处：classes 相等不是 raw
functions 的 pointwise equality；NF field 的加乘则是 normalize 后的函数，不能为其
FunLike coercion 无条件提供“coercion 保持 pointwise addition/multiplication”的规则。
在 pole cancellation 等情形，canonical evaluation 也不是到 ℂ 的 ring hom。
建议把 raw analytic 计算的 API 与 field equality 的 algebra API 清楚区分，
并使用已证明的 `toGerm_add/mul/inv`、normalization 等式在两者间转换。
高维必须改成忽略适当 analytic exceptional sets 的 equality 或使用 sheaf，
本轮没有把一变量 codiscrete quotient 冒充高维 field。

## Modular-function field 已通过的测试

实验 structure 的字段是直接 predicate：

```text
meromorphic : UHP.Meromorphic f
invariant   : ∀ γ∈Γ, ∀ τ, f(γ•τ)=f τ
at_cusps    : ∀ i, MeromorphicAtCusp (c i) f
```

c 包含正行列式 scaling matrix 和 positive width。
cusp condition 是存在 `F : ℂ → ℂ`、`MeromorphicAt F 0`，使得在 `atImInfty`
最终有 `f(c.scaling•τ)=F(qParam c.width τ)`。
这允许 cusp pole；checks 在 trivial Γ 上用 1/q 测试，不能用 modular forms 的 boundedness 代替。

三个字段均已证明对常数、加、负、乘、逆闭合。
随后 `toAmbient` 从 meromorphy proof 把原函数送入上半平面 classes field；
`modularSubfield` 选出**存在满足所有直接条件的代表**的 classes，并证明它是 Subfield。
`IsModularFunction.toField` 最后才产生 field element。
逆与 ambient field inverse 一致也已有证明，因此实际拿到了 Field instance 及 inverse-law check。
`IntegrationChecks.modularSheafSubfield` 还通过已证明的 ambient comparison，在 sheaf field
中实现相同 modular subfield；两条 raw predicate→field 路线的 agreement 也有显式 theorem。

此测试验证的是给定 cusp coordinates 的 closure 与 field 可行性，不是某个 Γ 的完整
modular-curve 理论：尚未枚举 Γ 的 cusps、证明 width/period 的合理性或建立 q-expansion API。
raw exact cusp equality 依赖 representative，不能无证明地说所有 codiscrete-equivalent
functions 都满足它；采用“存在好代表”的 Subfield 避开了这个逻辑错误。
Γ 参数的 GL 范围仅提供实验中的普通 invariance。与当前 mathlib 的
`SlashInvariantForm Γ 0` 对接应使用 `[Γ.HasDetOne]`：该版本 slash 含
`|det γ|^(k-1)`，所以 k=0 且 determinant 为正时仍有 `1/det γ` 因子，
仅正 determinant 不够。负 determinant 还会对函数值做 conjugation。
普通 invariant-functions field 本身正确，但不能直接把任意 GL 的 weight-zero slash
invariants 当作此 field；例如一般 Γ 的常数 1 未必 slash-invariant。
`ModularSlashChecks.lean` 已证明 determinant-one 情况的 iff、保持原函数的
`IsModularFunction.toSlashInvariantForm`，以及由 bundled slash form 加 analytic/cusp
条件恢复 modular predicate。checks 包括整数 modular group 子群的实际实例。

## Sheaf、Stacks 与更大的对象 B

[Stacks 01X1](https://stacks.math.columbia.edu/tag/01X1) 从 stalkwise regular sections
的 localization 再 sheafification 定义 meromorphic sheaf。regular 指 non-zero-divisor germ，
不要求 denominator 的 point value 非零。我们的 `coordinatePoleFraction` 正好验证这个区别：
`z-x` 在 x 值为零，但 germ regular，因而 `1/(z-x)` 可成为 sheaf section。

参考 [Zeta-Wu/MeromorphicFunction](https://github.com/Zeta-Wu/MeromorphicFunction)
实现已适配本项目 Lean/mathlib 版本，并保持 attribution；`SheafChecks.lean` 检查了一般定理：
connected、locally connected LRS，配 domain stalks 和 UniqueContinuation，
其 meromorphic global sections 是 field。在复平面上这些条件都已实例化。
这是实际 compiled Field，不是未经证明的设想。

`SheafLocalBridge.lean` 从 `MeromorphicAt f x` 构造 local holomorphic fractions，
证明其 denominators 在每个 stalk regular，再进入 localization 和 sheafification；
也证明 converse，因此直接 analytic predicate 有明确的局部 sheaf 意义。
`SheafGlobalBridge.lean` 进一步证明描述同一原始函数的局部分式在 overlap 上 cross-products
相同，localization 与 sheafification 后相同，因而可以 unique glue。
它实际构造 `MeromorphicOn f univ → X.meromorphicGlobalSections`。
`SheafOpenBridge.lean` 将 gluing 推广到任意开域，直接构造上半平面上的 meromorphic
sheaf section，因此并不局限于整个复平面的函数。
`SheafOpenField.lean` 把参考 global-sections field criterion 推广到一般 connected open，
给上半平面的 meromorphic sheaf sections 配出实际 Field。
`IntegrationChecks.modularToSheaf` 因而把直接 modular predicate 送入这一独立构造的 field。
`globalSection_congr` 还证明在复平面上改动 codiscrete exceptions 不改变所得 sheaf section。
`SheafArithmeticBridge.lean` 验证局部分式加乘与 section 运算一致；
`SheafQuotientBridge.toSheafRingHom` 给出复平面上的实际 RingHom，
`SheafOpenQuotientBridge.toSheafRingHomOn` 将其推广到任意复开集。
`SheafOpenInjective.sectionOn_eq_iff_codiscrete` 证明 section equality 恰好对应 codiscrete
equality，所以这个 map 在任意开集上 injective，不需要 connectedness 或 field structure。

反向并未止于设想：`SheafReverseBridge` 使用 sheafification 的 local surjectivity，
把任意 section 在每个点附近 lift 成 holomorphic localization fraction。
`SheafFractionEquality` 使用 local injectivity 与 localization cancellation，
从同一 section 的 lifts 得到 punctured-germ equality。
`NormalGluing` 正规化这些局部函数，让 overlap 上的实际 point values 相等后 glue。
`SheafSurjective.sectionOn_sheafRepresentative` 证明这个 NF representative 再 sheafify
恰好恢复原 section。
最后 `SheafEquivalence.toSheafRingEquivOn U` 是任意复开集上的完整 `RingEquiv`，
包括空集和不连通开集；`normalToSheafRingEquivOn` 在 connected nonempty 上把第三种
normal-representative field 也接入同构。
非空与连通只用于断言上述 rings 是 fields，未被塞入 analytic predicate 或 ring comparison。
`IntegrationChecks.lean` 检查 LF predicate 到 classes field 与 sheaf field 的两条构造路线，
以及 LF/chart predicates 到 local sheaf witnesses；均先给定 analytic proof，最后才产生 field element。

不能把 `Frac(O(X))` 与 `Γ(X,K)` 一概等同：前者要求一个 global numerator/denominator，
后者只需要 locally 给出 fractions。比如 compact connected Riemann surface 的 global
holomorphic functions 只有常数，而 meromorphic functions 可以非平凡。
两个 global fields 的 comparison 必须通过 local fractions、gluing 与 compatible equality，
不能靠同名 “field of meromorphic functions” 宣布 equivalent。
**本轮已证明 quotient↔NF、quotient↔sheaf、NF↔sheaf 的完整 RingEquiv，
并证明 direct analytic predicate 给出的 field element 在这些同构下相符。
sheaf comparison 已涵盖上半平面与任意复开集。**

超越 manifolds，可以研究 reduced complex analytic spaces 上的 meromorphic functions。
但是 connectedness 独自不足以保证 field：不同 irreducible branches 可产生零因子。
应把 predicate 的一般性与“何时得到 field”的假设分开。
对任意 LRS，尤其含 nilpotents 的非 reduced 对象，`f : M → ℂ` 的 point values
不足以表达结构层的数据；这时应使用本身更一般的 sheaf-section 语言。
因此没有一个保留所有 pointwise API 的无条件“最大 B”。
适合当前 mathlib 分层的是：通用解析流形 scalar predicate → 一维便利 API →
适当 equality 下的 algebra → 独立的 LRS sheaf 构造与 comparison。

## 验证、来源与剩余工作

统一入口：`XYin.PhD.Test.MMeromorphic`。在项目根目录运行：

```sh
lake build XYin.PhD.Test.MMeromorphic
```

版本：Lean `v4.30.0`；mathlib revision `2abc242511324144d08d214fc066915f01b900cc`。
checks 包含算术、chart independence、holomorphic pullback、ℂ/ℍ/Riemann-surface comparisons、
高维分式/逆、反例、三种一变量构造的 RingEquiv、modular Subfield、sheaf 双向 global bridge。
重要结果用 `#print axioms` 检查，仅标准 `propext`、`Classical.choice`、`Quot.sound`。
没有 sorry、admit、自定义 axiom 或 unsafe。
最终统一入口验证结果：`lake build XYin.PhD.Test.MMeromorphic` 成功，3249 jobs
（包含依赖与已验证目标的 replay），零 warning/error；31 个保留的 Lean 模块
均在该 import graph 内，另有统一入口本身。验证日期：2026-10-03。

来源：

- [指定 Zulip 讨论](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Elliptic.20functions.20.2F.20Field.20of.20meromorphic.20functions/with/616716742)。
- [Zeta-Wu sheaf 实现](https://github.com/Zeta-Wu/MeromorphicFunction/tree/main/MeromorphicFunction)：
  Basic blob `857308c2e3dc7cfae5202f6210a3dffdfda7c652`，
  ComplexPlane blob `80664cbe86b808d9bad1921dd23036abdc74057b`。
  `Reference/` 保留出处；主要适配 import、少量兼容写法和 transparency option。
- [ProjectVD field 实现](https://github.com/kebekus/ProjectVD/tree/main/VD/Field)：用于比较思路，
  本轮 quotient/NF files 是独立实现。
- [Stacks 01X1](https://stacks.math.columbia.edu/tag/01X1)。

尚未证明的内容不在当前实验的完成声明中：一般高维 analytic-space/LRS 的
pointwise-predicate comparison；任意复杂 Γ 的 cusp
分类/坐标独立性，以及有限 Laurent expansion、q-expansion 唯一性和 canonical NF 代表上的
modular conditions。ambient fields 的同构不会自动证明后面这些 modular-specific API。
一维 C¹→Cω 已有显式 theorem，但未注册为全局自动 instance。
这些是后续可拆分的 theorem/API 工作，不能通过弱化现有定义、改成 field membership
或给 comparison 添加 axiom 来填补。
这些不是给当前 field proofs 留下的假设洞：本轮的一维 global comparison 已经完成。
更广 setting 的比较需要重建对应 holomorphic structure sheaf，并选择适合其 exceptional
sets 的 equality，不能直接复制一变量的 codiscrete quotient。


## 后续：指定的指数增长 cusp 条件与 X(1) 源码核查

这一次先复用了已存在的 production 增长、normal-form 和 cusp-period 定理，再将正式
`ModularFunction` 的结构改成：

```lean
meromorphic' : MMeromorphicNF toFun
bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsExpBoundedAt toFun 0
```

`MMeromorphicNF` 在独立的 `ModularFunctions/ManifoldMeromorphic.lean` 中定义，只依赖
mathlib。它作用于 f 本身，不是 field membership。`toMeromorphicField` 随后由该
predicate 构造；`toFun_toMeromorphicField`、injectivity 和 field transport 均是证明。

normal representative 的选择沿用此前生产版本的约定；现在用独立 analytic predicate
表达它。不能以此给 NF raw pointwise sums/products 的 coercion 定理，因为 cancellation
后仍需 normalize。此前 quotient ↔ NF ↔ sheaf 的测试继续保留。

新的 cusp predicate 完全使用指定的 all-weight 公式：

```lean
def OnePoint.IsExpBoundedAt (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ) : Prop :=
  ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsOfExponentialGrowth (f ∣[k] g)
```

它与旧 weight-zero growth predicate 是 `Iff.rfl`；并不是把旧 q-meromorphy
condition 偷换一个名字。与常规 q-meromorphic cusp 条件的等价性是单独证明的。

| 新增文件 | 真正检查的内容 |
| --- | --- |
| `CuspGrowth.lean` | production 的 weighted-bound growth ↔ 正指数 big-O；requested formula 的展开 |
| `CuspGrowthCoordinates.lean` | all-weight scaling independence、单 scaling 双向测试、不同 weights 的乘法 |
| `CuspQEquivalence.lean` | 直接存在 exact meromorphic q-germ ↔ canonical cuspFunction meromorphic；raw eventual-holomorphy 和 NF 两个增长 iff |
| `BoundedNormalForm.lean` | punctured bound ⇒ NF analytic；normalize 后的 continuous bound 保留 |
| `ExpModularFunction.lean` | production 的独立 predicate 与 cusp 结构字段、之后才构造 field element、Field/ℂ-algebra/逆律 |
| `ManifoldPredicateChecks.lean` | production ↔ 原 independent chart predicate；C¹ 坐标独立性/复合、算术与 NF inverse |
| `OrbitCoordinate.lean`、`LevelOneOrbit.lean` | abstract bridge 及本地 j 实际实例化的 orbit quotient ≃ ℂ；明确只是集合层次 |
| `LevelOneField.lean` | 实际 `RatFunc ℂ ≃ₐ[ℂ] ModularFunction 𝒮ℒ`，保持常数并将 X 映到 j |
| `AffineFunctionField.lean`、`GeometricFunctionField.lean` | 独立 integral scheme 的 polynomial affine chart ⇒ function field 与 level-one modular field 同构；chart 为显式假设 |
| `P1Basic.lean`、`P1ChartRing.lean`、`P1Chart.lean`、`P1Proper.lean` | 独立的 Proj ℂ[X₀,X₁]、integral/非空实际 affine chart/ℂ-polynomial chart/实际 proper structure morphism |
| `P1Field.lean` | 无 chart 假设的实际 scheme function field ↔ modular field；geometric germ X₁/X₀ 映到 j |
| `PolynomialSpectrumPoints.lean` | over-Spec ℂ 的 affine-line points 与 ℂ 的实际等价；不混淆素理想与值点 |
| `LevelOneTopology.lean` | 实际 open quotient topology 下 ℍ/SL₂(ℤ) ≃ₜ ℂ |
| `AINTLIBSourceAudit.md` | 固定 main/dev 版本、j 的实际定理、X(1) 对象与解析比较的缺口 |

对于一张给定的 cusp chart，等价性只要求 NF、正 period 和 periodicity。
对于一般 slash-invariant Γ，all-cusp theorem 使用 `[DiscreteTopology Γ]` 与
`[Γ.HasDetPlusMinusOne]`，从 cusp stabilizer 得出正 period。`𝒮ℒ` 自动满足这些前提。
等价性的内容为 `c.IsExpBoundedAt f 0 ↔ c.IsMeromorphicAt f`；右端是周期 q 参数
在 0 处 meromorphic，允许有限阶 pole，不是 holomorphic/bounded-at-cusp。

这套 NF 假设有实质作用。raw meromorphy 允许在可去点任意修改值；一列这样的异常值
可以趋向 cusp，使 boundedness 不能推出 exact meromorphic q-germ，或使 inverse
失去 exponential growth。`CuspQEquivalence` 的 raw 版本明确保留 eventual holomorphy。

本地 Cox 理论已经证明 modular functions = ℂ(j)，本轮包装了实际的 ℂ-algebra
同构，不需要重新移植 AINTLIB 的 j-generation 证明。AINTLIB 有可复用的 j 满射
与 equal-j ⇒ same orbit 证明，但检索版本没有完成的
compact X(1) 以及其 meromorphic field 比较。不能把 source audit、条件式桥梁或
现有 SL₂(ℤ) field instance 报告成 `C(X(1)) ≃ₐ[ℂ] ModularFunction 𝒮ℒ` 的证明。
具体源文件、版本和后续路线见 `AINTLIBSourceAudit.md`。


进一步的几何实验已经完成标准 projective j-line 模型本身的 scheme function-field
同构。这里的左端独立定义为 `Proj ℂ[X₀,X₁]`，不是 modular functions 的别名；
其实际 polynomial chart、integral 性和 properness 都有 Lean 证明。
`P1Field.functionFieldModularEquiv` 将几何函数域的 ratio coordinate 送到 actual j。
这完成了标准代数模型意义下的函数域结论。

仍需区分另一项要求：将这个所选模型识别为一个独立构造的 compact analytic X(1)，
或某个 AINTLIB coarse-moduli/compactification 对象。当前上游没有完成的目标对象，
本轮没有捏造这种识别；open quotient 的 homeomorphism 也不能取代 compact analytic
structure / cusp / sheaf 比较。这个范围边界在源码核查文档中逐项说明。


本次最终累计验证：`lake build XYin.PhD.Test.MMeromorphic` 成功（4061 jobs）。
全部 49 个保留的 Test Lean 模块都由该入口覆盖。该次日志无 warning、error 或 sorryAx；
关键 predicate/cusp iff、field inverse law、实际 RatFunc 与 projective-line function-field
同构、properness 和 quotient-homeomorphism 的 axiom checks 均只有
`propext`、`Classical.choice`、`Quot.sound`。`git diff --check` 通过。
