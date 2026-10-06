# AINTLIB 的 X(1) 与函数域比较：源码核查

核查日期：2026-10-03。以下结论针对明确的源码版本，不是声称上游未来不会补全。

## 固定版本与检索范围

- AINTLIB main：`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`。
- `dev/modular-curves`：`dfc30e5082a97472b11138c5325b3acad7ec5071`。
- `dev/leanmodularforms`：`112d12d95e9c19f0d477b7a687bd49563ab8d07d`。
- main 使用 Lean `v4.35.0-rc3`、mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`。
  本项目仍使用原有 Lean `v4.30.0` 和 mathlib 版本，没有升级环境。
- 检查了 modular-curves 项目、LeanModularForms 的 j/orbit 文件、项目文档及上述分支的树。
  外部 checkout 只用于读取源码，没有把其未经编译的声明作为本项目证明依赖。

## 真正找到的对象与定理

| 源码 | 已有内容 | 对当前目标的作用 |
| --- | --- | --- |
| [ModularCurves/Basic.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/Basic.lean) | 模块入口与项目目标；namespace 内没有曲线定义 | 不能据此引用一个已完成的 X(1) |
| [Moduli/CoarseSpace.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/Moduli/CoarseSpace.lean) | `YHCoarse`、`YZeroCoarse`、`YOneFine` 等代数模问题的构造 | `YHCoarse` 取辅助 level 3 和全 GL₂ 子群可构造通常用于 Y(1) 的代数商；`xOneFine` 是椭圆曲线对象，不是紧化 X(1) |
| [Moduli/Coarse.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/Moduli/Coarse.lean#L86) | level-one j-line 的 coarse-points 目标 | `jLine_coarse_points`、`jLine_coarse_points_j`、`exists_coarse_gammaH` 的证明仍含 `sorry` |
| [JFunction.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/LeanModularForms/LeanModularForms/Modularforms/JFunction.lean) | `j`、`j_MDifferentiable`、`qj_tendsto_atImInfty`、`j_surjective`、`sameOrbit_of_j_eq_j`、`j_injOn_fdo` | 真实的解析输入，可以开始证明 open orbit quotient 的 j-coordinate 描述 |
| [ForMathlib/Orbits.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/LeanModularForms/LeanModularForms/ForMathlib/Orbits.lean) | `OrbitFM`、`orbFM` 等 quotient 包装 | 没有 j-induced homeomorphism 或 Riemann-surface atlas |
| [IrreducibilityScoping.lean](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/ModularCurve/IrreducibilityScoping.lean#L39) | 明确列出的 analytification、uniformisation、GAGA 缺口 | 上游也将这些标为未构造的基础设施 |

### Y(1) 的辅助 level 商：不能因 N ≥ 3 就排除 level one

`YHCoarse` 的 `N ≥ 3` 是其全 level 覆盖的要求，不能据此断言没有 Y(1) 的构造路线。
在 ℂ 上取 `N = 3`、`H = ⊤ : Subgroup (GL (Fin 2) (ZMod 3))`，
便得到 scheme `Y(3) / GL₂(ℤ/3ℤ)`，这是经典忘掉全部辅助 level 后构造 Y(1) 的方式。
源码中 `coarsePr_existsUnique_lift`（CoarseSpace:168）给出 categorical quotient 的
universal property，并有 quotient projection 的 integral、surjective 及结构映射 affine API。
这些比单纯写 `Spec ℂ[j]` 或一个待证明的 existence statement 更具体。

但是，当前源码没有将这一特化商识别为 `Spec ℂ[j]` 的已完成 isomorphism，
也没有将其 analytification 识别为 `SL₂(ℤ) \ ℍ` 的 theorem。
CoarseSpace 的说明本身将 geometric-points characterization 列为后续工作；
独立文件 Coarse 中的 level-one j-classification 仍有实际 `sorry`。
本段是源码级核查，不是对整个上游 dependency closure 的编译或 axiom 证书。
`YOneFine` 则定义的是 N ≥ 4 的 Y₁(N)，与 Y(1) 的名字和含义均应区分。

### Y₀(N) 与 X₀(N)

`CoarseSpace.lean:252–254` 有明确的 `YZeroCoarse` scheme 定义：
`YHCoarse (R := R) N hN hinv (borel N)`，其中 `hN : 3 ≤ (N : ℤ)`、
`hinv : IsUnit (N : R)`。`borel N` 的定义是 GL₂(ℤ/Nℤ) 中左下角为零的矩阵子群。
因此现成代码实际提供 Y(N) 的 Borel 商，以及上一节列出的通用 categorical quotient API。
N = 1、2 不能直接代入这个现成定义；这不排除使用更大的辅助 level 另行构造。
尚未找到此 scheme 的 analytification 与 Γ₀(N)\ℍ 的已完成识别定理。

main 与已核查的 `dev/modular-curves` 分支中，均未找到已完成的具体 X₀(N) 紧化。
仓库确有 `ForMathlib/FiniteAffineImageProjective.lean` 等一般 proper projective closure
基础设施，但没有找到将它们实例化并识别为 modular X₀(N) 的代码。
不能把一般射影闭包、开放曲线 Y₀(N) 或 Γ₀(N) 的群定义当作已完成的 X₀(N)。

`JFunction.lean` 中的 slash-invariance lemma 是 `private`；下游移植需要提供公开包装或
直接从定义复用已有 modular-form invariance。不能直接写一个不存在的公共 lemma 名字。

去掉注释和字符串后的源码检查显示，JFunction 的 86 个本地 import 模块没有
`sorry`、`admit`、自定义 `axiom`、`native_decide` 或 `implemented_by`。
这只是源码检查，**不是**在本项目环境编译该上游项目后的 kernel/axiom 证书。

## 所要求的定理尚不能从这些代码中直接实例化

数学上的目标应表达为一个自然的 ℂ-algebra equivalence，而不是 Lean 中两个不同类型的
字面 equality：

```text
C(X(1)) ≃ₐ[ℂ] ModularFunction SL₂(ℤ).
```

左边至少有两种独立含义：代数 integral curve 的 scheme function field，或紧 Riemann
surface 的 global meromorphic sheaf sections。两者的比较也需要单独的 theorem。
目前没有一个已完成的 AINTLIB `X(1)` 可供选定并填写这个声明的左端。
不能把左端直接定义为右端，也不能拿带 `sorry` 的 coarse-points 目标当作依赖。

## 可以怎样推进真正的比较

### 解析 quotient 路线

1. 用 j-invariance、surjectivity 和 equal-j ⇒ same orbit 建立 `ℍ / SL₂(ℤ) ≃ ℂ`。
   这是集合双射，尚不是 analytic equivalence。
2. 通过 holomorphic open mapping 建立 j-induced quotient homeomorphism。
3. 为 quotient 提供复结构，并在 elliptic stabilizer 点证明 meromorphic descent。
   那里的局部 quotient coordinate 是 `w²` 或 `w³`；只用 inverse-j 的集合函数不够。
4. 加入 cusp，用 `q = exp(2πiτ)` 与 j 的 simple pole 建立 `X(1) ≅ ℙ¹(ℂ)`。
5. 从独立的 manifold/sheaf meromorphy 定义出发，证明 pullback 与 descent 是互逆
   ℂ-algebra maps。当前已经完成的 exponential ↔ exact meromorphic q-germ API
   可以用于这个步骤的 cusp 部分。

### j-generation 路线与已经存在的本地实现

证明 `RatFunc ℂ ≃ₐ[ℂ] ModularFunction SL₂(ℤ)`，映射为 `R ↦ R(j)`。
一条经典证明是：证明只有有限多个 interior pole orbits；用 j 的多项式清除这些 poles；
再用 j 的多项式消除 cusp Laurent principal part；最后证明 everywhere holomorphic、
cusp-removable 的 weight-zero invariant function 为常数。

本项目的 `Cox/ModularFunction.lean` 已经完成这一条生成证明，
`Cox/ModularFunctionField.lean` 提供 `toMeromorphicField_eq_ratFunc` 和
`theorem_11_9_i_subfield`。本轮进一步将它包装为实际的
`LevelOneField.ratFuncModularEquiv : RatFunc ℂ ≃ₐ[ℂ] ModularFunction 𝒮ℒ`，
并检查 coordinate X 映到 `jModularFunction`、常数保持和 inverse roundtrip。
这也验证了本次更换 predicate/cusp 字段后，已有 Cox 生成理论继续适用。

本地 `Cox/LatticeJ.lean` 也已证明 j 满射与 orbit classification，因此
`LevelOneOrbit.lean` 已实际实例化 `ℍ / SL₂(ℤ) ≃ ℂ`；不依赖未经编译的上游 j。
随后 `LevelOneTopology.lean` 已通过复 open mapping theorem 将它升级为使用既有
quotient topology 的 `ℍ / SL₂(ℤ) ≃ₜ ℂ`。这已是实际 homeomorphism，仍不是
compact analytic atlas 或 sheaf descent theorem。

另外，`AffineFunctionField.lean` 已由 mathlib 的 fraction-ring 唯一性建立：
一个独立 integral scheme 的非空 affine chart 若有 section ring `ℂ[X]`，
其 function field 就与 `RatFunc ℂ` 同构；有兼容 complex-algebra 数据时是
ℂ-algebra equivalence。`GeometricFunctionField.lean` 将它与实际 modular-field
同构组合。这个一般定理保留明确的 chart 假设。

后续的 `P1Basic.lean`、`P1ChartRing.lean`、`P1Chart.lean` 已经独立构造标准模型
`P1.scheme := Proj ℂ[X₀,X₁]`、integral 性、实际非空 affine open D₊(X₀) 和它的
section-algebra equivalence。`P1Proper.lean` 还证明实际结构 morphism 到 Spec ℂ 为 proper。
`P1Field.lean` 因此使用**已经证明的实际 chart 数据**，给出无额外 chart 假设的：

```lean
MMeromorphicTest.P1.functionFieldModularEquiv :
  MMeromorphicTest.P1.scheme.functionField ≃ₐ[ℂ] ModularFunction 𝒮ℒ
```

另有实际 geometric germ `X₁/X₀` 映到 `jModularFunction`、常数保持和 inverse roundtrip
的 checks。左端采用 mathlib 的 scheme functionField，独立于右端的 modular-function
predicate。不是给 modular field 换名，也不是把左端定义成右端。

`PolynomialSpectrumPoints.lean` 识别的是 over-Spec ℂ 的真正 affine-line scheme points
与 ℂ，不能将 Proj 的 underlying homogeneous-prime points 当作 ℂ-valued points。

标准 projective j-line 是经典 level-one 曲线的代数模型。本测试还未给出将这个
所选模型与某个独立 compact analytic quotient / AINTLIB moduli object 识别的 theorem。
若将目标定义为这个标准模型，则其函数域比较已完成；若要求该额外几何识别，不能
省略它，也不能把 properness 与 open quotient homeomorphism 宣称为该识别的证明。

因此剩余问题不是再次证明 modular functions = ℂ(j)，也不是证明所选 projective
j-line 的函数域比较，而是将所选模型与要求的独立 X(1) 对象作几何识别。
这部分不能从当前 AINTLIB stub 或含 sorry 的目标推出。

## 当前可核验的结论

后续 `../ModularPolynomialCurve/` 实验进一步复用本地 modular-polynomial 与
Γ₀(N) field-generation 理论，建立独立 plane model 的 actual function field 比较及
实际 Γ₀(N) orbit quotient 到其零点的满射。详见该目录的 README；这仍不是与
AINTLIB `YZeroCoarse` 的 scheme identification，也没有将 raw plane curve
当作其 normalization。

本轮完成的是 cusp 定义及等价性、独立 analytic condition、其 field 接口，
实际的 rational-function/modular-field 同构、open orbit-quotient homeomorphism，
以及独立 proper projective j-line 的实际 scheme function-field 同构。
可以精确报告所选标准代数模型上的 field theorem 已完成。
不能把它报告成与一个未给出的 AINTLIB X(1) 定义的比较已经完成。
如需后者，必须提供实际源文件/版本，或继续独立构造 compact analytic quotient 并证明
其与所选 projective j-line 的结构比较。
