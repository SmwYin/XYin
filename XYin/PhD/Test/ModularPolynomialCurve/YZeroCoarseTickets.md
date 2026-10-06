# 实际 AINTLIB YZeroCoarse 比较：任务板

本轮只针对 pinned AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17` 的实际对象。
Lean/mathlib 在 `/private/tmp/xyin-y0-aintlib-work` 独立验证，XYin 工具链不变。
共享 `.mathlib-quality/tickets.md` 属于其他在途证明，故本轮任务单独记录。

| ID | 状态 | 具体目标、证明路线与来源 |
| --- | --- | --- |
| Y0-01 | CHECKED | 独立 Lean 4.35.0-rc3 / mathlib 300d0e5 环境。`Moduli.CoarseSpace` 构建成功 9375 jobs；实际 `YZeroCoarse`、representability、affineness、quotient lift 均只有三标准公理。 |
| Y0-02 | CHECKED | 实际 `YZeroCoarse ≅ Spec` Borel 不变量坐标环，以及 projection triangle、sections pullback/inclusion 已通过完整模块构建，关键声明只有三标准公理。 |
| Y0-03 | CHECKED | `GeometricJ.lean`：chart independence、global section gluing、任意 local presentation characterization、自然性、regular jMap、底环和 X 坐标公式均已在 pinned 环境通过编译，关键声明只有三标准公理。 |
| Y0-04 | CHECKED | 实际 source-j descent、投影/底环/任意 chart 坐标公式和 ℂ level-3 实例已通过统一模块构建，零自身 warnings，只有三标准公理。一般 affine deduction instance 收窄为 local。 |
| Y0-05 | AUDITED | `YZeroCoarseComparisonGaps.md` 已核查 quotient elliptic curve 的实际 sorry 以及 complex isogeny/lattice 连接的缺失。完整 Φ relation、finite birational 和 normalization 比较仍未证明。 |
| Y0-07 | CHECKED | 实际 fine smoothness、invariant inclusion integral、Noetherian 底环上的 coarse finite type、invariant-ring Noetherianity、quasi-compactness，以及全部 ℂ 特化已通过统一构建；只有三标准公理、零自身 warnings。 |
| Y0-08 | CHECKED | 实际 fine-to-coarse projection finite/surjective，global sections pullback injective；十文件统一构建 9400 jobs 通过，五个关键声明标准三公理。 |
| Y0-09 | CHECKED | 不假定 fine domain，从 smooth ℂ-algebra 的 local étale charts 证明 reduced，再经 inclusion 单射降到 invariants / actual coarse；统一构建通过，十个关键声明标准三公理。scoped 单声明 cleanup 的最终累计检查已通过。 |
| Y0-10 | CHECKED | 任意 algebraically closed field 上 reduced finite-type algebra 的 rational points 分离元素；统一构建通过，四个关键声明标准三公理，ℂ×ℂ 非-domain sanity 通过。 |
| Y0-11 | CHECKED | 实例化 actual coarse invariant ring，并将 algebra points 与 literal `Spec ℂ → YZeroCoarse` over-base morphisms 对应。actual source-j 复点坐标公式和 level-3 roundtrip sanity 也已通过严格模块构建；五个关键声明标准三公理。 |
| Y0-13 | CHECKED | actual 复代数点与 scheme points 的 lifting、实际投影/底环兼容性、fine 双向点对应、native elliptic curve/marking 及其 universal pullback 一致性均已 strict setup 检查通过；十一条关键检查 std3、零自身 warnings。2026-10-04 累计构建已通过。 |
| Y0-14 | CHECKED | actual invariant-ring restriction fibers 的 Borel-orbit 刻画，以及 literal scheme-point orbit Setoid / quotient ≃ actual coarse complex points 均通过严格构建。后者 9403 jobs、十条 std3、零自身 warnings，含代表元 rfl 与 level-3 双向 roundtrip；没有 freeness 假设。 |
| Y0-15 | CHECKED | `FieldGeometricJ` 对任意域的全局 pointed presentation、elliptic Weierstrass model 与 j 一致性严格模块构建通过，六声明 std3。actual coarse source-j = native ℂ-model j 的特化也已 strict setup 通过，2026-10-04 累计构建已通过。 |
| Y0-16 | CHECKED | 给定原生 E 的 actual classifier、pointed/cartesian iso、marking transport、source-j=给定 E 的 Weierstrass j，以及无需给定 marking 的 E-only existence 已 strict 编译通过；九条 std3、两种 level-3 sanity、零自身 warnings。 |
| Y0-17 | CHECKED | 实际 axis 的 closed immersion、finite/flat/lfp/rank、subgroup/killing 已验证二十八条 std3；独立 AxisGenerator 已用 order-divisor iso/ideal equality 和 all-T factor transfer 得到 HasExactOrder、identity fppf generator、IsCyclic、原生 GammaZeroStructure 与 actual coarse lift 存在性。命名严格构建 9410 jobs、二十六条 std3、四种 N3 sanity、自身零 warnings。 |
| Y0-19 | CHECKED | native classifier naturality 与 positive glSmul、HomOver→EllHom transport、fine point→native marking→classifier 的精确往返均通过严格命名编译。实际 GammaHClasses→actual coarse complex points 已 well-defined、保持给定 E 的 source-j 且满射；六条原始 std3、三种 N3 sanity，无自身 warning。逆向补齐于 Y0-20。 |
| Y0-20 | CHECKED | 同一 fine classifier 的 marked pointed iso、EllObj iso→原生 HomOver→EllHom 精确往返已验证。实际 class map 单射和 native GammaHClasses≃actual coarse complex points 已 strict named 编译通过，最终 class leaf 十三条 std3、五个 N3 sanity，无自身 warning。含代表元、source-j、inverse-on-marking、任意 full lift 的逆映射公式；fresh 实际源码/输出/产物审阅通过。 |
| Y0-12 | CHECKED (SCOPED) | 三项指定声明的单声明 cleanup、宽度/假设/搜索审计、profiler 和最终累计检查通过。fresh simplify 的跨文件 scalar API consolidation 建议保留未实施；无数学缺陷。报告单独保存 `Cleanup/`，共享 sidecar 不动；不声称全部 27 文件的完整 cleanup。 |
| Y0-18 | CHECKED | 任意交换环 actual projective model 的 geometric j、ofJ→actual coarse source-j 复点满射、实际 polynomial evaluation 及 ℂ[X]→B 单射均严格编译通过；共八条 std3、零自身 warnings，含 level-3 sanity；没有 B-domain 假设。三个新模块已纳入 27-file 累计构建。 |
| Y0-06 | CHECKED CHECKPOINT | 2026-10-04 06:54 UTC 历史累计验证28990 exit0 /9563jobs；99retained modules /935项逐模块公理checks /186sanity examples，own诊断0、无sorryAx/未许可公理/源码副本清单漂移。parent receipt与独立594-artifact provenance audit已保存；历史27/39/47/60/76 checkpoints独立保留。Y0-40至70已纳入历史99-module gate；之后临时实验另行验证。99模块fresh Lean编译先成功，验证器尾撇号漏计修复后复核成功。 |
| Y0-21 | CHECKED | `YZeroCoarseBorelAxis` 正向单位标签重编号与实际 Borel marking 换基保留固定 E 内 axis subgroup 的 literal immersion ideal；正确模块名严格编译通过，七项标准公理检查、三个 sanity（含 N=5 非自逆单位）、自身零诊断，独立源代码/输出/产物审阅通过。已纳入39-module累计 gate。 |
| Y0-22 | CHECKED | `YZeroCoarseSubgroupQuotientGeometry` 原始 subgroup quotient 的 Flat / Surjective / UniversallyClosed 通用证明及 actual chosen-killing wrappers，正确模块名严格编译 exit0，十一条标准三公理、自身零诊断；任意 base 的 literal axis 和 actual N=3 特化均通过。已纳入39-module累计 gate；未证明 Proper 或 quotient curve 的 elliptic upgrade。 |
| Y0-23 | CHECKED | `YZeroCoarseHopfGaloisLeft` 实际 Hopf–Galois equivalence 的左 B-algebra 升级正确模块名 strict exit0；底层 ring map 保持 rfl，两个 scalar/tensor sanity 通过，六项仅标准公理、自身零诊断。已纳入39-module累计 gate；局部 finite/étale 仍是后续目标。 |
| Y0-24 | CHECKED | `YZeroCoarseQuasiCompact` 通用 QuasiCompact.of_comp_surjective 及 raw quotient chosen-killing / literal axis wrappers 的正确模块名严格编译通过，七项标准三公理、两个 examples、自身零诊断，独立审阅通过。已纳入39-module累计 gate；不推断 Proper 或 finite type。 |
| Y0-25 | CHECKED | `YZeroCoarseHopfFinite` 通用 Hopf–Galois finite-module descent 与 actual free-patch wrapper 的正确模块名严格编译通过，八项标准三公理、两个 examples、自身零诊断，独立审阅通过；已纳入39-module累计 gate。无 Noetherian/domain 假设，尚非 global quotient projection finite。 |
| Y0-26 | CHECKED | `YZeroCoarseHopfEtale` 通用 Hopf–Galois étale descent、实际 groupRing appLE scalar alignment 与 free-patch wrapper 的正确模块名严格编译通过，八项标准三公理、两个 examples、自身零诊断，独立审阅通过；已纳入39-module累计 gate。明确保留几何输入 `Etale G.π`，不预先假设 quotient projection étale。 |
| Y0-27 | CHECKED | actual target quotient chart 原像与真实 IsPullback square 的正确模块名严格编译通过，八项标准三公理、一个 actual N3 example、自身零诊断，独立源码/输出/产物审阅通过；已纳入39-module累计 gate。 |
| Y0-28 | CHECKED | actual local quotient projection finite 与 explicit `Etale G.π` 下 local étale 的正确模块名严格编译通过，十三项标准三公理、两个 patch examples、自身零诊断，独立审阅通过；已纳入39-module累计 gate。 |
| Y0-29 | CHECKED | actual finite constant scheme projection、literal marked-axis subgroup projection 和 actual full complex point 特化 étale，正确模块名 strict exit0、五项标准三公理、两个 examples、自身零诊断，独立审阅通过；已纳入39-module累计 gate。 |
| Y0-30 | CHECKED | actual glued/public quotient projection finite 与 arbitrary Spec R / actual N3 axis wrapper 正确模块名 strict exit0、九项标准三公理、一个 example、自身零诊断。使用 target-local pullback comparison；无 Noetherian/domain/étale 假设；已纳入39-module累计 gate。 |
| Y0-31 | CHECKED | actual subgroup projection étale 时 actual glued/public quotient projection étale，literal axis 满足该输入；正确模块名 strict exit0、十二项标准三公理、两个 examples、自身零诊断；已纳入39-module累计 gate。 |
| Y0-32 | CHECKED | generic universally-closed surjective precomposition 的 separated descent、finite corollary、actual raw quotient chosen-kill / arbitrary-axis separated wrappers 已正确模块名 strict exit0，八项标准三公理、两个 examples、自身零诊断；未声称 quotient curve proper，已纳入39-module累计 gate。 |
| Y0-33 | CHECKED | Noetherian base 的 actual local quotient algebra finite-type、actual scalar alignment、clean étale faithfully-flat smooth descent 已 strict named exit0。LocalFT137：11 checks/3 examples；HopfSmooth132：24 checks/4 examples；零自身诊断，独立审阅通过；已纳入47-module累计 gate。 |
| Y0-34 | CHECKED | locally Noetherian base 上 actual quotient structure map finite type/finite presentation/proper，以及 explicit subgroup etaleness 下 smooth；literal axis wrappers 通过。FTProper218：13 checks/2 examples；SchemeSmooth126：15 checks/2 examples，均 strict named exit0、零自身诊断、独立审阅通过；已纳入47-module累计 gate。 |
| Y0-35 | CHECKED | rank comparison/forward 三模块已纳入47-module gate。新增 converse69、actual source-rank79、faithfully-flat descent67、actual coinvariant rank91、smooth-rank iff139、raw scalar local-dimension114、actual scheme dimension144 均 strict named exit0且独立审阅通过。最后 actual raw/public/axis quotient structure map 为 smooth relative dimension1，需 locally Noetherian base 和 étale subgroup；16 checks/2 examples，无 genus/model 假设。全部已纳入60-module累计gate，独立provenance审阅通过。 |
| Y0-36 | CHECKED | 通用 flat surjective scheme morphism 的 reduced/integral descent 和实际 E/G over任意field 的 integral wrappers 已 strict named12802 exit0（12 checks/4 examples）并纳入47-module gate；原生 E-field integrality 的六项 actual transitive checks 已 green。无需 Noetherian/étale/代数闭假设；尚无 quotient-genus、Weierstrass model 或 quotient-j 结论。 |
| Y0-37 | CHECKED | generic FiniteFunctionField118 与 actual raw/public/axis quotient native finite-injective pullback104 均 strict named exit0（16/3 与8/2），独立数学审阅通过；仅标准公理、零自身诊断，无预设 genus/model 或额外 scalar tower。两者已纳入60-module累计gate。 |


注意 fine GL₂ full-level scheme 可能不连通，不能假定其全局坐标环为整环。
Y0-02 不依赖该假设。函数域比较仍需证明 Borel quotient 的 integrality。
| Y0-38 | CHECKED | generic FunctionFieldFormallyUnramified57（7/1）、FunctionFieldEtale66（9/1）、actual quotient function-field étale106（10/2）均严格具名 exit0，只有标准公理、零自身诊断。actual wrapper 适用于任意域、subgroup étale；axis 自动提供，未假设 Noetherian/model/genus。泛型 field 可分/étale 不等于 places 无分歧，三者已纳入60-module累计gate。 |
| Y0-39 | CHECKED | native E→literal-k fieldWeierstrassModel scheme iso 与实际 over-base 公式已保留129、strict named94422exit0（13/1）并纳入60-module gate；模型/函数域相关真实 primitive closures onlystd3。尚未推出native k-algebra function-field equivalence/genus；常数图另行测试。 |
| Y0-40 | CHECKED INDIVIDUAL | 通用 Hopf stalk-rank comparison76 已 strict named1622exit0（8/2），仅 coefficientFinite/Flat 与actual Hopfdatum，无Noeth/Etale/domain/Free。数学/临时完整输出已root审阅，具名产物已核验。actual group-rank→local/global quotient-rank 仍需adapters；该leaf在60-module gate之后。 |
| Y0-41 | CHECKED INDIVIDUAL | actual projModel native RingEquiv 保持独立几何常数κW已保留104、strict named58776exit0（10allowed/2），root/j完整数学、命名产物与副本审阅通过。κW独立来自结构映射与泛型germ；任意Field、局部classical。post60，尚未推出nativeE代数同构或genus。 |

| Y0-42 | CHECKED INDIVIDUAL | native E的实际函数域 RingEquiv 已保留79、strict named82623exit0（8std3/2），逆模型诱导映射和复合公式与literal functionFieldMap均rfl；root审阅数学/具名产物通过。post60，常数图/AlgEquiv另行证明。 |
| Y0-43 | CHECKED INDIVIDUAL | actual G.HasRank r→groupRing stalk rank已保留109、strict named70194exit0（13std3/2），root/j完整审阅通过；无额外Free/Noeth/domain/Etale/model假设。post60，local/global quotient ranks为下一步。 |
| Y0-44 | CHECKED INDIVIDUAL | generic finite-flat dominant integral scheme map的实际函数域degree=scheme finrank，已保留126、strict named11602exit0（10std3/2）；完整germ/scalar square、实际affine pullback和具名六产物/C已root/j独立审阅。post60，无Noeth/genus/model假设。 |
| Y0-45 | CHECKED INDIVIDUAL | 任意integral schemes over Spec k的独立几何常数图及dominant函数域map自然性已保留77、strict named43285exit0（9std3/2），root/j完整数学/具名副本、六产物/C审阅通过；独立π/germ scalars与local top witness，无额外genus/model前提。post60。 |

| Y0-46 | CHECKED INDIVIDUAL | 实际native E函数域κE-compatible AlgEquiv 已保留124、strict named35261exit0（14allowed/4）；源Algebra显式由Eπ/germ独立定义，底层RingEquiv/RingHom rfl，root/aud完整数学与具名产物审阅通过。post60，尚无quotient genus/model。 |
| Y0-47 | CHECKED INDIVIDUAL | generic几何BaseAlgebra/tower/baseAlgHom 已保留82、strict named51208exit0（7allowed/2）；native函数域pullback不变，两端π/germ标量独立，root/invar具名副本/六+C产物审阅通过。post60。 |
| Y0-48 | CHECKED INDIVIDUAL | canonical local quotient rank93（13/2）和actual raw chart rank84（10/2）均strict named26773/34900exit0，只有标准公理、零诊断；实际Free patch+G.HasRank r推出局部rank r，root完整数学/具名产物审阅通过。post60，全局rank正在测试。 |
| Y0-49 | CHECKED INDIVIDUAL | genericFU+LFT scheme map在每个点的literalstalkMap扩张maximal ideal等式已保留76、strict named94633exit0（8allowed/2）；无domain/DVR/Noeth/genus前提，root完整数学/具名产物审阅通过。post60，actual quotient包装正在测试。 |
| Y0-50 | CHECKED INDIVIDUAL | actual glued quotient全局rank=r已保留76、strict named70148exit0（10std3/2），经真实quotientGlueData openCover与target-chart pullback，由local rank推进；actual free_gluePatch提供局部Free。root及两名peer完整源码/输出/具名产物审阅通过；无额外globalFree/Noeth/Etale/domain/model假设。post60。 |
| Y0-51 | CHECKED INDIVIDUAL | NativeCoordinateFractionField116、strict named77344exit0（9allowed/2），实际coordinate scalar/tower/IsFractionRing保持独立几何κE；root/aud完整审阅通过。post60，未加入polynomial/RatFunc/genus结论。 |
| Y0-52 | CHECKED INDIVIDUAL | generic FullConstantFieldDescent51、strict named47973exit0（4allowed/2），任意k-AlgHom映入full-constant field即可反射常数；root/j完整审阅通过。post60，无finite/separable/genus假设。 |
| Y0-53 | CHECKED INDIVIDUAL | actual E→E/G native函数域degree=真实subgroup rank已保留114、strict named87582exit0（11std3/2）；任意field、public chosen-kill及native complex N3 sanity，root/invar完整数学审阅通过。post60，无Noeth/Etale/genus/model输入；不是coarse/Phi函数域比较。 |
| Y0-54 | CHECKED INDIVIDUAL | actual raw/public/axis quotient全部点的literalstalkMap最大理想等式已保留99、strict named43740exit0（12std3/2）；arbitrary base、真实Etale Gπ输入，actual N3 sanity，root/j审阅通过。post60，无DVR/domain/genus假设。 |
| Y0-55 | CHECKED INDIVIDUAL | IntegrallyClosedLocalizationCover81：strict41277exit0，8项std3/2API/零诊断；spanning basic-open cover上非零away localizations整闭推出domain整闭，无有限型/Noeth/光滑假设，root/invar数学审阅通过。post76。 |
| Y0-56 | CHECKED INDIVIDUAL | FaithfullyFlatIntegrallyClosed94：strict16318exit0，12项许可公理/2API/零诊断；源环domain/normal与actual FF给出目标环整闭，真实principal-ideal contraction，无finite/Etale/genus。post76。 |
| Y0-57 | CHECKED INDIVIDUAL | native RR两个leaf3036jobs exit0，9项primitive-only检查std3；NativePolynomialScalars100、NativeRatFuncScalars102、NativeFunctionFieldStructure80均strict named exit0，10/12/9项许可检查、各2API、零自身诊断；原生警告单独保存。post76。 |
| Y0-58 | CHECKED INDIVIDUAL | actual raw/public/axis独立κQ-compatible AlgHom136：strict43768exit0，12项std3/3真实API/零诊断；真实over-base triangle与函数域map自然性，底层map rfl，root/peer审阅通过。post76。 |
| Y0-59 | CHECKED INDIVIDUAL | LocallySmoothIntegrallyClosed73：strict28410exit0，9项std3/2API/零诊断；actual locally standard-smooth relative1 domain借助Y0-55整闭，无全局standard/Noeth/model前提。post76。 |
| Y0-60 | CHECKED INDIVIDUAL | NativePatchBaseField61、NativeChartIntegrallyClosed91：strict45124/45808exit0，7/11项许可检查、各2API、零診断；真实非空base open=top，实际ΓSpec ring equivalence保留运算，源整性+光滑1给出真实gluePatch chart整闭。post76。 |
| Y0-61 | CHECKED INDIVIDUAL | NativeFullConstantField77、NativeGenus80：strict49100/21372exit0，11/12项std3、各2API、零诊断；独立几何κE下实际模型pack给出源函数域满常数域与intrinsic genus=1。仅源E结论。post76。 |
| Y0-62 | CHECKED INDIVIDUAL | ClosedPointStalkDVR93：strict25578exit0，10项std3+1项无公理、2API、零诊断；任意域上光滑relative1 scheme的闭点actual stalk同时domain+DVR，不预设integralX/DVR。post76。 |
| Y0-63 | CHECKED INDIVIDUAL | FlatStalkIntegrallyClosed71：strict20245exit0，7项std3/2API/零诊断；真实flat local stalk map忠实平坦，借助Y0-56下降整闭性，surjective wrapper覆盖所有点，无finite/Etale/Noeth前提。post76。 |
| Y0-64 | CHECKED INDIVIDUAL | actual商函数域满常数域86：strict77108exit0，10项std3/2真实κQ API/零诊断；只用actual独立几何AlgHom与源fullconstants，root/peer完整数学审阅通过。post76。 |
| Y0-65 | CHECKED INDIVIDUAL | actual源及商stalk整闭92：strict42501exit0，14项许可checks/2API；商affine sections整闭96：strict91105exit0，12项std3/2API，均零诊断。generic affine引理只要求DomainΓ；actual raw/public wrappers无额外Etale/Noeth/normality前提。post76。 |
| Y0-66 | CHECKED INDIVIDUAL | DVRPlace72、StalkBaseAlgebra76、SchemeClosedPointPlace99：strict55252/82099/34263exit0，8/6/11项许可checks、各2API、零诊断；独立几何常数与literal stalk fraction field给出真实闭点Place及实际stalk image membership。post76。 |
| Y0-67 | CHECKED INDIVIDUAL | actual raw/public商函数域存在超越元素115：strict17095exit0，12项许可checks/2API/零诊断；源RatFunc只用于源transcendence，经真实finite AlgHom algebraicity塔反证商algebraicity。未假设旧X在商中、分离性或genus。post76。 |
| Y0-68 | CHECKED INDIVIDUAL | StalkRamificationIndex104：strict25534exit0，9项std3/2actual API/零诊断；任意FU+LFT map的actual stalk maximal prime长度定义指数=1，raw/public quotient真实Etale subgroup供给输入。不是尚未建立的RR valuation比较。post76。 |
| Y0-69 | CHECKED INDIVIDUAL | DVRPlaceValuation67：strict11004exit0，6项std3/2API/零诊断；真实adic surjectivity与integer ordered normalization唯一性给出intrinsic Place valuation=actual DVR adic valuation，无额外归一化前提。post76。 |
| Y0-70 | CHECKED | generic实际stalk与函数域pullback square99，strict named15461exit0，11项std3/2identity+raw商API/零诊断；仅dominant+irreducible，不预设integral/field/DVR/finite/closedness。已纳入99-module累计gate。 |

Y0-55至69的独立具名检查现在均已纳入99-module checkpoint；各行post76指其原始检查时间。

以下条目均在99-module checkpoint之后，已分别通过正确模块名的严格编译，
现已纳入126-module累计检查。历史99记录保持不变。
每个leaf保留两个实际API检查及完整公理输出。

| ID | 状态 | 具体结果和适用边界 |
| --- | --- | --- |
| Y0-71 | CHECKED INDIVIDUAL | `GenericPointOverBase`：结构映射独立常数的真实 generic-spectrum triangle；6 checks/2 APIs，零诊断。 |
| Y0-72 | CHECKED INDIVIDUAL | `DVRPlaceLocalUnramifiedValuation`：实际兼容的两个DVR及函数域、local FU+EssFT映射，推出归一化valuation相等；8/2，零诊断。未假定额外Flat/TorsionFree。 |
| Y0-73 | CHECKED INDIVIDUAL | `RatFuncTranscendentalParameter`：任意域扩张的超越参数给出保留原常数的RatFunc AlgHom，X与多项式限制公式；11/2，零诊断。 |
| Y0-74 | CHECKED INDIVIDUAL | `NativeCoordinateTowerObstruction`：实际商若容许旧source RatFunc通过真正塔下降，则subgroup rank整除2；rank3 API推出矛盾；5/2，零诊断。 |
| Y0-75 | CHECKED INDIVIDUAL | `IntrinsicPlaceResidueFinite`：实际finite separating chart的每个intrinsic place具有有限residue field及正degree；7/2，零诊断。chart假设明确保留。 |
| Y0-76 | CHECKED INDIVIDUAL | `ProperPlaceLift`：真正proper integral scheme上，任意place具有保留generic及base triangles的valuative lift；8/2，零诊断。未推断闭中心或恢复。 |
| Y0-77 | CHECKED INDIVIDUAL | `FiniteFieldPointClosed`：separated scheme上的实际有限扩域值点像为闭点；5/2，零诊断。无全局有限型或proper假设。 |
| Y0-78 | CHECKED INDIVIDUAL | `SchemeClosedPointPlaceValuation`：dominant FU+LFT映射两端闭点的实际stalk归一化valuation兼容；14/2，零诊断。两端smooth relative1，无预设交换方块。 |
| Y0-79 | CHECKED INDIVIDUAL | `RatFuncTranscendentalParameterFinite`：真正函数域的任意超越参数有限性及AlgHom自然性；11/2，零诊断。未使用旧坐标下降。 |
| Y0-80 | CHECKED INDIVIDUAL | `RatFuncSubfieldParameter`：映入真正函数域的任意k子域，其超越参数也有限；8/2，零诊断。无需嵌入有限性输入。 |
| Y0-81 | CHECKED INDIVIDUAL | `ProperPlaceClosedCenter`：有限residue field使实际over-base lift中心为闭点，proper wrapper给出带闭中心的lift；9/2，零诊断。residue有限性仍明确输入。 |
| Y0-82 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientClosedPointPlaceValuation`：实际raw/public商的闭点像自动闭，真实étale subgroup给出闭点places的valuation兼容；16/2，零诊断。尚非所有places结论。 |
| Y0-83 | CHECKED INDIVIDUAL | `DVRPlaceRecovery`：包含实际DVR像的非平凡place等于DVR构造place；4/2，零诊断，独立审阅通过。 |
| Y0-84 | CHECKED INDIVIDUAL | `RatFuncParameterScalars`：新超越参数的实际polynomial/RatFunc塔及原常数公式；5/2，零诊断。 |
| Y0-85 | CHECKED INDIVIDUAL | `PlaceCenterStalkSquare`：仅不可约scheme的真实generic lift强制中心stalk到generic stalk交换方块；8/2，零诊断。Place client另加integral。 |
| Y0-86 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientParameterFinite`：任意域上实际raw/public商自身的每个超越参数均有限；10/2，零诊断。无Etale/Noeth/genus/model或旧坐标下降假设。 |
| Y0-87 | CHECKED INDIVIDUAL | `NativePlaceResidueFinite`：任意域上原生E的所有intrinsic places有有限residue和正degree；8/2，零诊断，独立审阅通过。全部chart输入从真实native pack推出。 |
| Y0-88 | CHECKED INDIVIDUAL | `ProperPlaceRecovery`：真实generic lift闭中心的stalk place恢复原place，proper+有限residue给出闭点表示；12/2，零诊断，独立审阅通过。 |
| Y0-89 | CHECKED INDIVIDUAL | `DVRPlaceAlgEquiv`：native DVR RingEquiv保留真实k标量，并给出正逆像在分式域中的字面公式；7/2，零诊断，独立审阅通过。 |
| Y0-90 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientParameterFunctionField`：任意域上的实际商参数给出三条scalar towers和finite FunctionField；特征零另得separable；11/2，零诊断，独立审阅通过。 |
| Y0-91 | CHECKED INDIVIDUAL | `StalkPointOverBase`：任意scheme的canonical stalk-spectrum点保留独立几何base algebra；6/2，零诊断，独立审阅通过。无需integral/irreducible/affine X。 |
| Y0-92 | CHECKED INDIVIDUAL | `NativePlaceGeometry`：任意域上原生椭圆曲线的每个intrinsic place均由真实闭点表示；7/2，零诊断，独立审阅通过。无额外residue/chart/CharZero输入。 |
| Y0-93 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceResidueFinite`：特征零实际raw/public商所有places有有限residue及正degree；10/2，零诊断。无Etale/Noeth/genus/model/parameter/chart输入。 |
| Y0-94 | CHECKED INDIVIDUAL | `SchemeClosedPointPlaceLift`：实际stalk AlgEquiv给出canonical lift，generic/base triangles及centre=x均正式证明；14/2，零诊断。无proper/residue/假设centre或square。 |
| Y0-95 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceRestriction`：任意域实际étale subgroup商的每个source intrinsic place都有target place，使normalized valuation在literal FF pullback下相等；8/2，零诊断，独立审阅通过。尚非surjective place map或genus公式。 |
| Y0-96 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceGeometry`：特征零实际étale subgroup商的每个intrinsic place均有真正闭点表示；9/2，零诊断，独立审阅通过。无外加chart/residue/model/genus假设。 |
| Y0-97 | CHECKED INDIVIDUAL | `SchemeClosedPointPlaceInjective`：separated integral smooth relative1 scheme上的closedPointPlace单射，由真实canonical lifts及valuative uniqueness证明；9/2，零诊断，独立数学审阅通过。先前具名receipt的parser元数据已修复，Lean证明不变。 |

Y0-71至97均已纳入2026-10-04 08:24 UTC的126-module记录：1171checks、240examples、
9590jobs，独立audit同时检查756项canonical artifacts。`CHECKED INDIVIDUAL`
标记保留其最初逐文件验证的历史；不表示仍在累计范围之外。

## 126-module checkpoint之后的具名检查

| ID | 状态 | 具体结果和适用边界 |
| --- | --- | --- |
| Y0-98 | CHECKED INDIVIDUAL | `SchemeClosedPointPlaceEquiv`：proper integral smooth relative1曲线的真实闭点-place双射，通用版显式保留all-residue-finite，native E任意底域自动供给；9checks/2双向API，root实际审阅通过。 |
| Y0-99 | CHECKED INDIVIDUAL | `PrincipalDivisorValuation`：intrinsic normalized valuation等于主除子系数的负指数；保留native finite/separating chart输入，无fullconstant/genus；8/2，root审阅通过。 |
| Y0-100 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceMap`：实际raw/public place restriction、valuation公式及真实闭点图像公式；任意域+Etale Gπ，无Q全部places表示/CharZero；12/2，root及两项peer审阅通过。 |
| Y0-101 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceEquiv`：CharZero+Etale Gπ下raw/public Q的闭点-place双射；原始独立κQ、无model/genus；10/2，root审阅通过。 |
| Y0-102 | CHECKED INDIVIDUAL | `FinsuppFiniteFiberPullback`：finite-fiber map的真正有限支撑加性拉回，support只需Zero、hom只需AddZeroClass，不要求单射；Bool→Unit二对一API；9/2，root审阅通过。 |
| Y0-103 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPlaceMapFiniteFibers`：任意域+Etale Gπ的实际place map有限纤维；source闭点表示、target闭点place单射及实际finite投影，未使用CharZero/target全places表示；11/2，root及peer审阅通过。 |
| Y0-104 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientDivisorPullback`：实际raw/public QDivisor→+EDivisor及系数公式，真正多对一有限纤维；任意域+Etale Gπ；9/2，root及peer审阅通过。 |
| Y0-105 | CHECKED INDIVIDUAL | `PrincipalDivisorPullback`：通用真实φ/r/hfib/hval及两套独立scalar/chart packs推出主除子兼容；9/2，root及peer审阅通过。 |
| Y0-106 | CHECKED INDIVIDUAL | `YZeroCoarseSubgroupQuotientPrincipalDivisorPullback`：CharZero+Etale Gπ的真实raw/public商主除子兼容；Q自身τ/ht及实际finite/separable packs，不加model/genus/chart输入；15/2，root及peer审阅通过。 |

以上九个条目不计入历史126 receipt；现已全部纳入最终135-module冻结检查点：
2026-10-04 09:19 UTC，9599jobs/1263checks/258examples，独立audit检查810项canonical产物。
具名历史标记保留；当前完整验证见`Cleanup/Cumulative135Verification.md`。
