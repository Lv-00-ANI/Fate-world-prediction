# L5-规则层与FCA · 模块设计意图

> 96 个模块。来源：`Fate/*.lean` 的模块文档、类型骨架、核心定义。
> 本文件由 `extract_intent.py` 自动生成，**未经人工复核**。


---

## `Frame`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Frame
> 阶段：**阶段 0 —— 定义与签名冻结**（规格 `02-证明路线/01-路线图.md` §阶段 0）
> **+ 作者裁决 Q-1 / Q-2 的落实**（`作者裁决-Q1到Q6.md`）
> 本文件做什么
> 给出规格 `01-路线图.md` §阶段 0 「范围」栏所列的**其余定义**：

**类型骨架**（7 个）：

- `structure Frame` (L22)
- `inductive ObservationRegime` (L71)
- `structure CtxSpace` (L94)
- `structure LocalDomain` (L103)
- `structure Rule` (L110)
- `structure RuleWithTheta` (L175)
- `structure ThetaIsExtracted` (L222)

**核心定义**（9 个）：

- `Yun` (L38)
- `currentRegime` (L79)
- `ObservedState` (L85)
- `DetRule` (L126)
- `Rule` (L135)
- `Rule` (L181)
- `RuleWithTheta` (L193)
- `ThetaStableOn` (L227)
- `ThetaIndependent` (L297)

**定理**：共 13 条，其中名字含主定理特征的 3 条：

- `thetaIndependent_of_exists_rule` (L305)
- `exists_rule_of_thetaIndependent` (L317)
- `degenerate_iff_thetaIndependent` (L337)

---

## `Classification`

**模块自述**：

> 命运理论 · FCA 分类系统层（作者裁决 N + O 的落点）
> ⚠ 本文件的定位与诚实边界（须先读）
> **作者裁决 N**：FCA 不再承担主线入口（`enc`），**改作分类系统**。
> **作者裁决 O**：因果进入分类循环 —— 循环的内容是**抽象与解构**（两种目光）。
> ⚠ 一、为什么本文件【重新实现】而不是【复用】`RealTemporalLayer`
> `FCA-副本/03-哲学依据/FCA的拓展与补足.md` 提议补「要素层 + 目光」，

**类型骨架**（4 个）：

- `inductive Gaze` (L29)
- `structure Temporal` (L39)
- `structure TemporalAction` (L192)
- `structure CycleStructure` (L418)

**核心定义**（28 个）：

- `Temporal` (L47)
- `IsElement` (L57)
- `IsConcept` (L60)
- `suspend` (L78)
- `gazeUp` (L95)
- `gazeDown` (L98)
- `HasUpper` (L107)
- `HasSplit` (L110)
- `temporalAction` (L203)
- `Temporal` (L213)
- `temporalFunctor` (L232)
- `Temporal` (L259)
- …另 16 个

**定理**：共 75 条，其中名字含主定理特征的 19 条：

- `isElement_iff_no_upper` (L113)
- `isElement_iff_no_split` (L117)
- `shouldStop_mono_tau` (L397)
- `shouldStop_monotone` (L405)
- `isClosedAttr_iff_closed_of_operator` (L465)
- `isModel_iff_isClosed_attrClosureOperator` (L487)
- `histInertia_eq_zero_iff` (L522)
- `gradForce_eq_zero_iff` (L569)
- `gradForce_nonneg_iff` (L582)
- `gradForce_mono_pointwise` (L613)
- …另 9 条

---

## `ComposeUnified`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.ComposeUnified`
> 阶段：**∘ 的融合结构 —— B 族主导，A 族为特例分支（作者第 465 轮裁决，读法一）**
> (a) 作者裁决（第 465 轮，逐字）
> > 「裁决1 b和a到底什么讲清楚 然后为什么不能构造一个融合的 以b为主导
> >   a是b（推广后）的一种特例」

**类型骨架**（3 个）：

- `class Composite` (L13)
- `class CommutativeComposite` (L18)
- `class DirectedComposite` (L23)

**核心定义**（1 个）：

- `directedCompInstance` (L50)

**定理**：共 7 条


---

## `RuleLevel`

**模块自述**：

> 命运理论 · 规则层级（Rule Level）
> 模块：`Fate.RuleLevel`
> 上游：`Fate/LawRule.lean`（`LawRule`，位于命名空间 `Fate.LawRule`）、
> `Fate/Frame.lean`（`CtxSpace`、`OutSpace`）、
> `Fate/Basic.lean`（`StateSpace`）。
> 问题（作者原问）

**类型骨架**（3 个）：

- `inductive RuleTag` (L10)
- `structure TrajPattern` (L35)
- `inductive RuleBody` (L46)

**核心定义**（5 个）：

- `RuleBody` (L68)
- `RuleEnc` (L169)
- `RuleBody` (L174)
- `RuleEnc` (L177)
- `composeTrans` (L228)

**定理**：共 16 条，其中名字含主定理特征的 5 条：

- `level_unique` (L81)
- `level_transition_iff` (L92)
- `level_trajectory_iff` (L103)
- `level_eq_iff_same_form` (L145)
- `encode_fst_eq_iff` (L183)

---

## `Alpha`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Alpha
> 阶段：**阶段 1B —— 依作者裁决 D 把 α 具体化为「取概念过程」**
> 裁决依据（**最高优先级**）
> `_规格/03-规范与裁决/01-作者裁决C-最彻底.md` **裁决 D**：
> > ### 裁决 D：α 具体化为 FCA 的取概念过程

**类型骨架**（2 个）：

- `structure Encoder` (L24)
- `structure E8BoundForm` (L198)

**核心定义**（6 个）：

- `Encoder` (L31)
- `takeConcept` (L114)
- `Encoder` (L158)
- `alphaOnQuotient` (L175)
- `Encoder` (L189)
- `E8Holds` (L210)

**定理**：共 16 条，其中名字含主定理特征的 4 条：

- `takeConcept_mono` (L126)
- `models_iff_takeConcept_subset` (L135)
- `alpha_respects_equiv` (L167)
- `e8Holds_mono` (L239)

---

## `AlphaStatistical`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaStatistical`
> 阶段：**α 的统计版本 —— 经验条件核 + 置信带，及「何时 `IsPoint`」的判据**
> 本文件补什么（与 `Fate.Alpha` / `Fate.LawRule` 的分工）
> `Fate.Alpha`（裁决 D）把 α 做成 **FCA 取概念过程** `takeConcept`——
> 那是 α 在**属性侧/概念侧**的版本。

**类型骨架**（2 个）：

- `structure Sample` (L32)
- `structure Band` (L123)

**核心定义**（10 个）：

- `cell` (L43)
- `count` (L48)
- `outs` (L59)
- `rawEmpirical` (L70)
- `empirical` (L76)
- `ball` (L136)
- `statAlpha` (L143)
- `Coverage` (L159)
- `BandCollapse` (L164)
- `SelfInBand` (L239)

**定理**：共 13 条，其中名字含主定理特征的 2 条：

- `statAlpha_isPoint_iff` (L169)
- `isPoint_iff_coverage_of_separating_zero` (L306)

---

## `FourOperators`

**模块自述**：

> §统一  **四算子统一框架**：α / γ / ∘ / υ
> **来源**：规格 `01-理论/10-命运理论-净版.md` 第 5 章
> 「规则层与 FCA」§5.3「四个操作：抽象、泛化、组合、完善」。
> ## 四个算子（规格 §1.4 符号表逐字）
> | 算子 | 名称 | 规格类型 | 本实现载体 |
> |---|---|---|---|

**类型骨架**（2 个）：

- `structure Framework` (L21)
- `inductive OperatorStatus` (L145)

**核心定义**（6 个）：

- `alpha` (L41)
- `alphaUpsilonComposite` (L122)
- `absorptionCandidates` (L131)
- `operatorStatus` (L153)
- `pendingOperatorObligations` (L172)
- `alphaObligationClosed` (L180)

**定理**：共 15 条，其中名字含主定理特征的 1 条：

- `alpha_mono` (L61)

---

## `GammaOperator`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.GammaOperator
> 阶段：**阶段 1C —— 泛化算子 γ 的类型签名与基本代数律**
> 本文件的地位与诚实边界（**必须先读**）
> 1. **本文件零 `sorry`、零 `admit`、零 `axiom`**（全部定理自建证明）。
> 2. **理论文档只给了 γ 的类型，未给精确定义。** 规格

**类型骨架**（2 个）：

- `structure GenOp` (L31)
- `class RuleSpec` (L283)

**核心定义**（12 个）：

- `IsGeneralized` (L68)
- `IsMinGeneral` (L148)
- `NonDegenerate` (L151)
- `IsLegitGeneralization` (L178)
- `gammaFCA` (L223)
- `alphaFCA` (L226)
- `gammaApply` (L308)
- `GeneralizationAdmissible` (L333)
- `IsMinGeneralRule` (L369)
- `RuleNonDegenerate` (L373)
- `LegitRuleGeneralization` (L377)
- `IsGeneralization` (L450)

**定理**：共 41 条，其中名字含主定理特征的 13 条：

- `monotone` (L54)
- `isGeneralized_iff_mem_range` (L71)
- `mem_range_iff` (L95)
- `comp_contracting_monotone` (L103)
- `comp_idempotent_iff` (L109)
- `comp_is_genOp_iff_idempotent` (L126)
- `nonDegenerate_iff` (L155)
- `isMinGeneral_bot_iff` (L169)
- `isLegitGeneralization_iff` (L182)
- `gammaApply_mono` (L318)
- …另 3 条

---

## `GazeAlgebra`

**模块自述**：

> 命运理论 · 三种目光的代数结构（作者裁决 I 的文献纪律 + 作者裁决 R 的加强纪律）
> ⚠ 本文件的定位与诚实边界（须先读）
> **任务**：查文献中「三种目光」能否构成某代数对象（如三元素格、Kleene 代数），
> 并写出 Lean 陈述。
> 一、`Gaze` 的出处与本文件的关系
> `Gaze`（`none` / `up` / `down`）已存在于本项目两处：

**类型骨架**（2 个）：

- `inductive G` (L18)
- `inductive SymLE` (L222)

**核心定义**（5 个）：

- `neg` (L266)
- `swap` (L298)
- `G` (L344)
- `G` (L359)
- `projMul` (L366)

**定理**：共 22 条，其中名字含主定理特征的 1 条：

- `negation_exists_but_unmotivated` (L328)

---

## `MVFCAPositive`

**模块自述**：

> MVFCA 肯定方向构造 · 第三种格：**块划分 ⊗ 层细化**（grid-block lattice）
> 本文件把 `MVFCA-肯定构造分析.md` 的结论落成可编译引理。**自包含**：只 import
> Mathlib，不 import 任何 Fate 模块（与既有证明解耦）；零 sorry / admit / axiom。
> §0  结论速览
> (A) **普适障碍（定理，格无关）**：在任意「完全格 + 标准闭包 `cl A = (A^□)^□`」
> 的模式结构里，`univ` **恒为闭集**（`univ_closed`）。故若 `maxdiam` 对

**类型骨架**（2 个）：

- `structure PatStruct` (L16)
- `structure BlockLayer` (L67)

**核心定义**（9 个）：

- `up` (L25)
- `down` (L28)
- `cl` (L31)
- `IsClosed` (L34)
- `InOneBlock` (L78)
- `upCl` (L82)
- `downCl` (L89)
- `bcl` (L94)
- `BIsClosed` (L97)

**定理**：共 17 条，其中名字含主定理特征的 2 条：

- `extent_diam_bound` (L136)
- `extent_diam_bound_of_inOneBlock` (L156)

---

## `Rule1Genuine`

**类型骨架**（2 个）：

- `structure ZSCM` (L26)
- `inductive Node3` (L651)

**核心定义**（19 个）：

- `ZOf` (L47)
- `joint` (L52)
- `zMass` (L57)
- `doLaw` (L61)
- `doCondZ` (L65)
- `obsLaw` (L70)
- `condFiberNum` (L76)
- `NoiseReadsX` (L83)
- `NoiseWeaklySeparated` (L169)
- `Rule1Premise` (L174)
- `zBad` (L345)
- `zGood` (L348)
- …另 7 个

**定理**：共 54 条，其中名字含主定理特征的 6 条：

- `noiseReadsX_iff` (L87)
- `fiber_y_unique` (L192)
- `exists_del_direction_attains_sup` (L770)
- `del_direction_threshold_iff` (L780)
- `del_direction_sup_sharp` (L788)
- `del_direction_exists_max` (L795)

---

## `RuleSyntaxGenOps`

**模块自述**：

> 规则核心链 · **四算子 / 概率-微分-迭代 / 可执行判定 在线性有序域上的泛化**
> （GEN-1 审计 §3 排名 3）
> ## 本模块做什么
> `Fate/RuleSyntaxGen.lean` 只把**语法类型与语义**（`TermK` / `eval` / `holds`）
> 搬到了任意线性有序域 `K` 上，但 `RuleSyntaxOps`（四算子 `γ / υ / ∘ / α`）、
> `RuleSyntaxExt`（`prob` / `deriv` / `iter`）、`RuleExec`（`check` 可执行判定）

**类型骨架**（2 个）：

- `inductive ExtTermK` (L137)
- `inductive TermQK` (L243)

**核心定义**（11 个）：

- `trueTermK` (L23)
- `generalizeK` (L33)
- `loosenK` (L47)
- `refineK` (L70)
- `composeK` (L84)
- `alphaFromK` (L112)
- `ExtTermK` (L148)
- `ExtTermK` (L205)
- `TermQK` (L266)
- `TermQK` (L274)
- `TermQK` (L284)

**定理**：共 28 条，其中名字含主定理特征的 9 条：

- `holds_refineK_iff` (L77)
- `holds_composeK_iff` (L87)
- `holds_alphaFromK_iff` (L117)
- `holds_iterK_iff` (L177)
- `holds_iterK_mono` (L192)
- `holds_iterK_prob_iff` (L198)
- `holds_composeK_self_of_forall` (L390)
- `holds_iterK_of_forall` (L399)
- `alphaFromK_succ_implies` (L426)

---

## `AlphaFCAConstruction`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaFCAConstruction`
> 阶段：**α 的 FCA 版本 —— 端到端完整构造（实例集 → 形式背景 → DG 基 → 规则）**
> 本文件补什么
> `Fate.Alpha`（裁决 D）给出 α 的**动作**：`takeConcept B := K.closureOp B`；
> `Fate.Implication` / `Fate.Completeness` 给出 **DG 基**与**完备性**。

**类型骨架**（1 个）：

- `structure AlphaData` (L25)

**核心定义**（5 个）：

- `alpha` (L223)
- `alphaQuot` (L271)
- `HasPseudoIntentSubset` (L298)
- `rulesUnionOf` (L302)
- `ceData` (L419)

**定理**：共 44 条，其中名字含主定理特征的 7 条：

- `models_iff_takeConcept_subset` (L136)
- `mem_dgBasis_iff` (L153)
- `dgBasis_sound` (L158)
- `exists_thIter_eq_thClosure` (L195)
- `dgBasis_complete` (L200)
- `rulesUnionOf_mono` (L354)
- `rulesUnionOf_mono_trans` (L396)

---

## `ComposeOperator`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.ComposeOperator
> 阶段：**规则层 · 组合算子 ∘ 的独立化**
> 任务
> 实现「组合算子 ∘」，给出：
> 1. **类型签名**：依规格 `03-规范与裁决/04-符号与方程规范.md` §一 的符号表，

**类型骨架**（1 个）：

- `structure MeasurableRule` (L75)

**核心定义**（12 个）：

- `ComposeAssoc` (L37)
- `ComposeRightUnit` (L46)
- `ComposeLeftUnit` (L52)
- `ComposeLaws` (L58)
- `rule'` (L107)
- `idRule` (L125)
- `comp` (L143)
- `pow` (L254)
- `IsKernelComposition` (L306)
- `IsSubmonoid` (L319)
- `composeOperatorObligations` (L325)
- `composeOperatorDelivered` (L335)

**定理**：共 14 条


---

## `FCA`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.FCA
> 阶段：**阶段 0 收尾 + 阶段 1B 启动**（依裁决 D）
> 本文件做什么
> 1. **阶段 0 部分**：FCA 层的**定义**——
> 形式背景 $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$、

**类型骨架**（1 个）：

- `structure FormalCtx` (L24)

**定理**：共 14 条，其中名字含主定理特征的 4 条：

- `mem_polarUp_iff` (L51)
- `mem_polarDown_iff` (L56)
- `subset_polarUp_iff_subset_polarDown` (L61)
- `concept_le_iff_extent_subset` (L112)

---

## `Implication`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Implication
> 阶段：**阶段 1B —— 框架自有条件命题 / 真正的自建数学**
> 本文件为什么必须自建
> **实测核验（可复核）**：Mathlib **无**蕴含基相关内容。
> 在 `D:\mathlib\packages\mathlib\Mathlib` 下检索以下关键词，**命中数全为 0**：

**类型骨架**（1 个）：

- `class FiniteAttrs` (L208)

**核心定义**（10 个）：

- `Models` (L28)
- `IsClosedAttr` (L77)
- `IsPseudoIntentCore` (L91)
- `IsPseudoIntent` (L108)
- `dgRule` (L152)
- `DGBasisSelfRef` (L155)
- `DGBasis` (L163)
- `synClosureOne` (L175)
- `synClosureIter` (L226)
- `chainBound` (L279)

**定理**：共 34 条，其中名字含主定理特征的 10 条：

- `models_iff_subset_polarDown` (L35)
- `models_iff_models_closure` (L54)
- `closureOp_mono` (L72)
- `isClosedAttr_iff_exists` (L80)
- `isPseudoIntent_iff` (L118)
- `dgbasis_sound` (L167)
- `models_iff_subset_semClosure` (L200)
- `synClosureIter_mono` (L264)
- `dgbasis_sound'` (L307)
- `exists_minimal_nonclosed` (L318)

---

## `Pairing`

**模块自述**：

> §0  配对接口：唯一与真实数据格式耦合的地方（作者确认）
> **裁决来源**：作者原话
> * 「我不知道哇 这种细节我的确没思考过」（对策略 B 的具体形式）
> * 「可以那就这样」（确认本方案）
> ## 设计原则
> **不为「配对策略 B 到底是什么」做选择** ——

**类型骨架**（1 个）：

- `structure Pairing` (L13)

**核心定义**（7 个）：

- `adjacent` (L20)
- `grouped` (L24)
- `direct` (L28)
- `transitions` (L37)
- `preAttr` (L48)
- `postAttr` (L52)
- `TransRule` (L56)

**定理**：共 5 条，其中名字含主定理特征的 3 条：

- `mem_transitions_iff` (L41)
- `transRule_mono_pre` (L72)
- `transRule_mono_post` (L77)

---

## `Rule2Genuine`

**模块自述**：

> `Fate/Rule2Genuine` —— **缺口 3：规则 2 的真语义版本**
> （第 248 轮）
> ## ⚠⚠ 一、本文件要修的是哪一条
> **第 247 轮 J1 的审核结论**（见 `Fate/Rule23Semantic.lean` 文件头）：
> | 定理 | 证明体 | 判定 |
> |---|---|---|

**类型骨架**（1 个）：

- `inductive XZY` (L22)

**核心定义**（16 个）：

- `setX` (L45)
- `setZ` (L48)
- `rk` (L51)
- `medChainAdj` (L59)
- `medChainG` (L81)
- `MediatorHypothesis` (L87)
- `directAdj` (L95)
- `directG` (L119)
- `MediationInvariant` (L135)
- `MassOne` (L145)
- `Supplied` (L148)
- `ZIsRoot` (L152)
- …另 4 个

**定理**：共 54 条，其中名字含主定理特征的 10 条：

- `exists_medFactor_of_invariant` (L139)
- `doLaw2_eq_doLawX_iff` (L218)
- `invariant_iff_not_readsX` (L418)
- `invariant_iff_no_X_Y` (L457)
- `carrierGraph_differs_from_medChain` (L484)
- `carrierGraph_true_differs_from_medChain` (L489)
- `exists_exchange_order_attains_sup` (L557)
- `exchange_threshold_iff` (L564)
- `exchange_sup_sharp` (L572)
- `exchange_exists_max` (L579)

---

## `RuleActivation`

**模块自述**：

> 规则层 · **动态激活机制**（全参与 + 按需激活）
> ## 作者澄清的机制（不是「从集合里挑一条」）
> 世界模型里规则的运作**不是**「从一个规则集合中选出一条来用」，而是：
> 1. **开始全部激活** —— 初始状态下全部规则处于激活态；
> 2. **数据进来部分不激活** —— 观测数据把一部分规则判为「不适用」（`suppressed`）；
> 3. **按需立即重新激活** —— 一旦某个**已激活**的规则依赖某条被抑制的规则，

**类型骨架**（1 个）：

- `structure Activation` (L16)

**核心定义**（4 个）：

- `Coherent` (L25)
- `closure` (L29)
- `fromData` (L141)
- `readDep` (L172)

**定理**：共 23 条，其中名字含主定理特征的 7 条：

- `closure_unique` (L66)
- `closure_mono_init` (L76)
- `closure_mono_dep` (L85)
- `closure_mono` (L95)
- `mem_closure_iff` (L106)
- `closure_mono_reads` (L176)
- `transGen_dep_mono` (L236)

---

## `RuleEvaluation`

**模块自述**：

> 命运理论 · **规则评价框架**（科学哲学驱动的半启发式框架）
> 模块：`Fate.RuleEvaluation`
> (a) 作者第 537 轮裁决的原话
> > 「**规则的评价这个属于半启发式  你按照科学哲学的相关处理方法来就行了
> >   各种科学观啊  剃刀啊  什么的   主要是很启发式吧   所以我认为净版这个不完整
> >   而且这个属于启发式辅助  需要加一个抽象  因为后续可能会有增删改**」

**类型骨架**（1 个）：

- `class RuleEvaluation` (L14)

**核心定义**（2 个）：

- `Better` (L28)
- `realEval` (L79)

**定理**：共 7 条，其中名字含主定理特征的 1 条：

- `realEval_better_iff` (L89)

---

## `RuleExec`

**模块自述**：

> 规则核心链 · **IR 提取到可执行**（乙-3）
> ## 本模块做什么
> `RuleSyntax.lean` 的语义层用 `ℝ`（不可计算）与 `Prop`（不可执行）：
> * `RuleTerm.eval  : RuleTerm → Env → ℝ      `
> * `RuleTerm.holds : RuleTerm → Env → Prop   `
> 本模块建立**可执行镜像**：

**类型骨架**（1 个）：

- `inductive Term` (L17)

**核心定义**（5 个）：

- `Term` (L32)
- `Term` (L40)
- `Term` (L52)
- `run` (L128)
- `trueTermExec` (L221)

**定理**：共 11 条，其中名字含主定理特征的 2 条：

- `run_iff_holds` (L131)
- `run_eq_false_iff_not_holds` (L137)

---

## `RuleReadSetWiring`

**模块自述**：

> `Fate/RuleReadSetWiring` —— **把 `RuleReadSet` 的依赖结构接进 `WorldModelCompleteV2`**
> ## (a) `RuleReadSet` 是什么（如实登记）
> `Fate/RuleReadSet`（36 定理，此前全库**零扇入、零消费**）做的是
> **「规则之间的依赖关系分析」**：
> | 名字 | 含义 |
> |---|---|

**类型骨架**（1 个）：

- `structure RuleSetWithDeps` (L17)

**核心定义**（4 个）：

- `dep` (L30)
- `activation` (L43)
- `lawRuleOf` (L167)
- `lawRuleFamOf` (L173)

**定理**：共 24 条，其中名字含主定理特征的 5 条：

- `dep_iff` (L38)
- `ruleDep_refl_iff` (L71)
- `determinesAt_of_wmc_iff` (L201)
- `exists_dec_of_wmc` (L236)
- `exists_preorder_family` (L252)

---

## `RuleSyntax`

**模块自述**：

> 规则核心链 · **IR 语法层**（乙-1）
> ## 本模块做什么
> 把「规则」从**数学语义**（`Set (Measure Y)`）升级为 **CIC 语法项**
> （一个 `inductive` 类型），并给出**语义解释** `denote` / `toLawRuleWith`。
> ## 为什么这满足「直接基于 CIC 和三条公理」
> * `RuleTerm` 是 Lean 的 **`inductive` 类型** ⟹ 本身就在 CIC 里；

**类型骨架**（1 个）：

- `inductive RuleTerm` (L20)

**核心定义**（2 个）：

- `RuleTerm` (L45)
- `RuleTerm` (L53)

**定理**：共 5 条，其中名字含主定理特征的 1 条：

- `holds_and_iff` (L165)

---

## `RuleSyntaxExt`

**模块自述**：

> 规则核心链 · **IR 语法扩展层**（乙-2 第 2 件）
> ## 本模块做什么
> 乙-1 的 `Fate.RuleSyntax.RuleTerm` 覆盖：变量 / 等式 / 不等式 / 算术 / 复合；
> 乙-2 第 1 件 `Fate.RuleSyntaxOps` 在其上给出四算子 `α / γ / υ / ∘`。
> `_audit/IR-1-规则CIC语法层.md` 的对照表登记了三项**未覆盖**要素：
> * **概率声明**（「以概率 ≥ p 成立」）

**类型骨架**（1 个）：

- `inductive ExtTerm` (L16)

**核心定义**（1 个）：

- `ExtTerm` (L29)

**定理**：共 5 条，其中名字含主定理特征的 4 条：

- `holds_iter_succ_iff` (L55)
- `holds_iter_iff` (L62)
- `holds_iter_mono` (L78)
- `holds_iter_prob_iff` (L180)

---

## `RuleSyntaxGen`

**模块自述**：

> 规则核心链 · **IR 语法层的线性有序域泛化**（GEN-1 审计 §3 排名 1）
> ## 本模块做什么
> `Fate/RuleSyntax.lean` 把 IR 语法固化在 `ℝ` 上
> （`abbrev Env := ℕ → ℝ`，`RuleTerm.const (c : ℝ)`）。
> 本模块**新增**一个对任意线性有序域参数化的语法类型 `TermK K` 与语义
> `TermK.eval` / `TermK.holds`，并证明：**在 `K = ℝ` 时，泛化版与 `ℝ` 版逐点一致**

**类型骨架**（1 个）：

- `inductive TermK` (L15)

**核心定义**（3 个）：

- `TermK` (L40)
- `TermK` (L49)
- `TermK` (L96)

**定理**：共 5 条


---

## `UpsilonOperator`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.UpsilonOperator
> 阶段：**阶段 1B —— 完善算子 υ 的代数律**
> 依主控解释（`/-! ...

**类型骨架**（1 个）：

- `structure IsCompletion` (L57)

**核心定义**（9 个）：

- `refineToUpsilon` (L49)
- `Saturated` (L86)
- `IsCompletion` (L188)
- `SaturatedSets` (L196)
- `fcaUpsilon` (L227)
- `UpsilonContracting` (L263)
- `orbit` (L368)
- `injectHistory` (L495)
- `nonnegClosure` (L556)

**定理**：共 47 条，其中名字含主定理特征的 14 条：

- `saturated_iff` (L113)
- `upsilon_le_iff_le_saturated` (L153)
- `isCompletion_iff` (L173)
- `fca_saturated_iff_isClosedAttr` (L240)
- `t6_10_unique_fixedPoint` (L267)
- `t6_10_fixedPoint_unique` (L273)
- `t6_10_convergence_rate` (L283)
- `t6_10_tendsto_iterate` (L291)
- `upsilon_join_compatible_iff` (L323)
- `orbit_mono_iterate` (L390)
- …另 4 条

---

## `WiringFCAAlpha`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.WiringFCAAlpha
> 任务：**W1-最高优先 接线** —— 把 `Fate.T112FCASpecific` 的具体 FCA 结果
> 接到规则层 α（`Fate.Alpha` / `Fate.InstanceChain.AlphaOutput`）。
> 本文件做什么
> `Fate/T112FCASpecific.lean` 此前是**孤立的**：已证明，但无任何下游消费。

**类型骨架**（1 个）：

- `structure AlphaSpecPartial` (L235)

**核心定义**（8 个）：

- `alphaRead` (L28)
- `K3X` (L163)
- `K3Ctx` (L170)
- `K3Y` (L173)
- `alphaPartition` (L181)
- `k3Rule` (L199)
- `k3Rules` (L203)
- `alphaReadOutput` (L230)

**定理**：共 23 条，其中名字含主定理特征的 3 条：

- `extent_eq_iff_intent_eq` (L42)
- `alphaRead_extent_iso_impossible` (L112)
- `alphaRead_lattice_iso_exists` (L120)

---

## `Adjunction`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Adjunction
> 阶段：**阶段 1B —— `takeConcept` 与 `polarUp`/`polarDown` 的伴随性**
> ## 标记图例（第 609 轮加，统一口径）
> - `[外部已证·Mathlib 引用]` —— 上游（Mathlib）已证，本框架直接引用；**不构成未完成义务**
> - `[已登记 · 未实现]` —— 该条以 Bool/Prop 字段登记了「未实现」的状态；**登记本身已证**

**定理**：共 16 条，其中名字含主定理特征的 1 条：

- `polar_adjoint_iff` (L33)

---

## `AlphaAndStochasticWiring`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaAndStochasticWiring`
> 任务：**② α（抽象侧）、④ 随机轨迹（生成侧）的接线**（不是造新模块）
> 本文件做什么
> C6 主干地图实测：`Fate.AlphaFCAConstruction`（α 的 FCA 版本，41 定理）与
> `Fate.TrajGenStochastic`（方案二，7 定理）**内容完整但扇入 0**——

**核心定义**（1 个）：

- `alphaDataOfInstances` (L37)

**定理**：共 23 条


---

## `AlphaAndStochasticWiringConsumer`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaAndStochasticWiringConsumer`
> 任务：**消费** `Fate.AlphaAndStochasticWiring` 的核心结论（P5 并行批次）
> 本文件做什么
> `Fate.AlphaAndStochasticWiring` 把两条孤岛接进主干：
> * 阶段 1：`alphaDataOfInstances : Finset (InstanceChain.Instance O A) → AlphaData`

**核心定义**（2 个）：

- `encoderAttrs` (L37)
- `encoderOfInstances` (L42)

**定理**：共 10 条


---

## `AlphaConcreteInstance`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.AlphaConcreteInstance
> 阶段：**阶段 1B —— α（取概念过程）的完整具体实例**
> 本文件做什么
> `Fate.Alpha` 里 α 是 `takeConcept B = closureOp B`——**一个具体函数**，
> 但该文件**没有给出任何一个具体的 (G, M, I)**。

**核心定义**（5 个）：

- `I3` (L19)
- `frame3` (L229)
- `enc3` (L241)
- `eqv2` (L270)
- `embed2` (L273)

**定理**：共 38 条，其中名字含主定理特征的 2 条：

- `alpha_mono_instance` (L179)
- `alpha_respects_equiv_instance` (L284)

---

## `AlphaDataConsumed`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaDataConsumed`
> 阶段：**把 `AlphaFCAConstruction` 的 α 定理真正「消费」到
> `WorldModelCompleteV2.alpha` 字段上（三条桥 + 两条附属）**
> 本文件补什么（一句话）
> `Fate.WorldModelCompleteV2` 的 `alpha` 字段**类型本来就是** `Fate.AlphaData`

**定理**：共 7 条


---

## `AlphaDataToLawRule`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaDataToLawRule`
> 阶段：**P2 桥的第 2 半 —— 规则提取（`dgBasis` → `LawRule`）**
> (a) 真实签名（贴原文核对，非推测）
> `Fate/LawRule.lean:69`：
> ```

**核心定义**（1 个）：

- `dgToLawRule` (L69)

**定理**：共 11 条，其中名字含主定理特征的 1 条：

- `dgRule_respected_iff_of_obs_eq` (L49)

---

## `AlphaDataToPartition`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaDataToPartition`
> 阶段：**P2 桥的第 1 半 —— `AlphaData.alpha` 的商化给出「划分的一块」**
> 本文件做了什么（一句话）
> 在真实类型上定义 **α 纤维块** `alphaCell D e`，并证明它确实是
> 「α 值相等」这一等价关系的**一块**（自反 / 对称 / 传递 / 就是等价类），

**核心定义**（1 个）：

- `alphaCell` (L25)

**定理**：共 15 条，其中名字含主定理特征的 3 条：

- `mem_alphaCell_iff` (L29)
- `alphaCell_eq_iff_mem` (L54)
- `alphaCell_proper_family_empty_iff` (L148)

---

## `AlphaFourOp`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.AlphaFourOp
> 任务：**AA6 —— 把 `Fate.WiringFourOpFixed` 接进 `Fate.Alpha`**
> 本文件做什么（一句话）
> `Fate.WiringFourOpFixed` 在同**一个**实例 `K3` 上证明了 α／γ／υ／∘ 四算子的
> 一致性（`four_operators_joint_compatibility` 等），但那些定理全部陈述在

**定理**：共 33 条，其中名字含主定理特征的 6 条：

- `alphaK_mono` (L47)
- `alphaK_models_iff` (L51)
- `alpha_upsilon_fixed_iff` (L58)
- `alpha_mono_upsilon` (L86)
- `comb_mono_left` (L149)
- `comb_mono_right` (L155)

---

## `AlphaFourOpConsumer`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.AlphaFourOpConsumer`
> 阶段：**P5-甲 —— `Fate.AlphaFourOp` 的消费方**
> 本文件做什么（一句话）
> `Fate.AlphaFourOp` 给出了 α／γ／υ／∘ 四算子交互的**一般**结论
> （`alpha_chain_collapses`、`alphaK_absorbs_comb`、`alpha_upsilon_same_fixed_set`、

**定理**：共 12 条，其中名字含主定理特征的 1 条：

- `chain_closed_iff_compute` (L28)

---

## `AlphaKernel`

**模块自述**：

> §6  Q-3 的消解：抽象等价关系取为 α 的**核**（作者授权）
> **来源**：作者裁决 —— Q-3「按最优最强的方向走」（授权消解）
> ## 问题（Q-3 / A31）
> 规格 A31 说「抽象 = 实例集在等价关系下的商」，但**未给等价关系 $\sim_{\mathcal E}$ 的判据**。
> 此前实现把它作**外置参数**（`AbstractEquiv E := Setoid E.Carrier`），
> 于是 T1B.2b（α 保结构）成为**条件定理**，前件 `RespectsEquiv` 待裁。

**核心定义**（2 个）：

- `alphaKernel` (L16)
- `alphaOnKernelQuotient` (L34)

**定理**：共 4 条，其中名字含主定理特征的 1 条：

- `equiv_le_kernel` (L60)

---

## `AlphaKernelAudit`

**模块自述**：

> Fate.AlphaKernelAudit
> **审计问题**：`α` 是否保持了抽象等价（`AlphaKernel` 里的核）？给出条件与证明。
> 结论（一句话）
> **是，且无条件**（`rfl` 级，零公理）。
> 但**"保持"有两种含义，必须分清**：
> | 问法 | 答案 | 定理 | 前件 |

**核心定义**（4 个）：

- `auditFrame` (L40)
- `auditCtx` (L48)
- `auditEnc` (L54)
- `auditE` (L61)

**定理**：共 4 条，其中名字含主定理特征的 2 条：

- `kernel_iff` (L14)
- `respectsEquiv_imp_le_kernel` (L31)

---

## `AlphaMVFCA`

**模块自述**：

> §0  从 MVFCA 闭包到 `α` 的局部域划分（作者裁决 O2 的落实）
> ## 背景
> **作者裁决 O2**：**「局部域 = 读集」**，即「规则依赖的情境就是它所在的局部」。
> **作者裁决 O4**：**降级 = 未证项记录**（中间状态，不是终点）。
> ## 本节做什么（作者裁决「建构的建构」）
> 把 `MVFCA4.PatStruct` 的闭包结构接到 `Fate.InstanceChain` 的 `AlphaOutput` 上，

**核心定义**（2 个）：

- `minClosed` (L19)
- `closedPartition` (L34)

**定理**：共 6 条


---

## `AlphaOf`

**模块自述**：

> §0  `α` 的具体实现：由 `target` 构造的完整 `AlphaSpec` 实例
> ## 背景
> `InstanceChain.AlphaSpec` 有五条要求（S1–S5）。前一轮 `alphaStructure` 已证其合取。
> **本节把它们打包成一个具体的 `α : Alpha D C X Y`，并证明 `AlphaSpec α`。**
> ## 这个实现是什么
> ```lean

**核心定义**（3 个）：

- `alphaOf` (L20)
- `LearnKGap` (L63)
- `LearnTargetGap` (L67)

**定理**：共 3 条


---

## `AlphaRulesLocal`

**模块自述**：

> §0  `RulesLocal`：从局部域构造规则（`α` 的另一半）
> ## 背景
> `InstanceChain.RulesLocal p rs` 要求：
> ```lean
> ∀ r ∈ rs, ∀ c x y, y ∈ p x → r c x = r c y
> ```

**核心定义**（1 个）：

- `localRuleAsLaw` (L20)

**定理**：共 4 条


---

## `CategoricalStratification`

**模块自述**：

> §53  ⭐⭐ **范畴层的档位分层**（推广 `Set` 层的 `cardStratification`）
> ## 背景
> **`Set` 层已有**（`Fate/Counterfactual.lean`）：
> $$\text{三情形} = \kappa\ \text{分层中的两个退化层}\ \{1\} \cup \{=\#F\}$$
> 且**任意有限档数** $n$ 的穷尽劈分已给出（`cardStratification`）。
> **`Fate/KernelQuotientCategorical.lean` 已给出范畴层的前三档**：

**定理**：共 5 条


---

## `Compactness`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Compactness
> 阶段：**阶段 1B 延伸——属性蕴含的紧致性（compactness）**
> 本文件回答的问题
> 规格把属性蕴含 $A\Rightarrow B$ 做成**全称命题**（见 `Fate.Implication`
> 的 `Models`）。全称命题的**紧致性**问题是自然的：

**核心定义**（4 个）：

- `Kce` (L89)
- `Ace` (L101)
- `Bce` (L104)
- `nG` (L139)

**定理**：共 11 条，其中名字含主定理特征的 2 条：

- `exists_finite_subset_same_polarDown` (L36)
- `exists_finite_subset_same_closure` (L77)

---

## `Completeness`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Completeness
> 阶段：**阶段 1B —— DG 基完备性**（规格 T1A.10 的「完备」一半）
> 本文件证明什么
> 规格 `02-证明路线/01-路线图.md` **T1A.10**：
> > `DG 基是最小完备蕴含基`｜前件：**形式背景有限**｜类别 ①

**核心定义**（8 个）：

- `DrivingLemma` (L63)
- `iterReachesClosure` (L77)
- `IsModel` (L112)
- `IsModelOf` (L238)
- `IsNonRedundant` (L252)
- `abstractStep` (L295)
- `deconstructStep` (L298)
- `oneRound` (L301)

**定理**：共 30 条，其中名字含主定理特征的 9 条：

- `exists_minimal_nonclosed_subset` (L81)
- `model_iff_closed` (L141)
- `completeness_Mod_eq_Int` (L145)
- `dgbasis_complete_semantic` (L151)
- `exists_synClosureIter_stabilize` (L162)
- `isModel_iff_isModelOf_dgbasis` (L242)
- `loop_monotone` (L311)
- `loop_fixpoint_iff_concept` (L317)
- `oneRound_iterate_mono` (L324)

---

## `ComposeDefault`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.ComposeDefault`
> 阶段：**裁决 A 的落地 —— (甲)「更强」+ (乙)「默认」两者兼得**
> (a) 作者裁决（第 484 轮，逐字）
> > 「a 甲乙」
> 其中「甲乙」指裁决 A 的两个读法**都要**：

**核心定义**（2 个）：

- `measurableRuleComposite` (L19)
- `defaultComp` (L56)

**定理**：共 6 条


---

## `ComposeEmbedding`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.ComposeEmbedding`
> 阶段：**裁决 1 要件 3「A 是 B（推广后）的特例」—— 读法三（嵌入）的判定**
> (a) 作者裁决 1 的原话（第 465 轮，逐字）
> > 「裁决1 b和a到底什么讲清楚 然后为什么不能构造一个融合的 以b为主导
> >   **a是b（推广后）的一种特例**」

**定理**：共 5 条，其中名字含主定理特征的 1 条：

- `trivial_embedding_exists` (L56)

---

## `ComposeSemantics`

**模块自述**：

> `Fate/ComposeSemantics.lean` —— **∘ 的两种语义不可同时成立**
> ## 背景（净版开放问题 5.1，`:1923` 逐字）
> > **[开放问题] 开放问题 5.1（组合的语义未定）**
> >
> > 组合 $R_1\circ R_2$ 的**语义**是什么——**是两条规则前后相接、是条件分布的边缘化、
> > 还是规则集的并**？原文未给。

**定理**：共 4 条


---

## `ConceptLatticeComplete`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.ConceptLatticeComplete
> 阶段：**阶段 1A 的实质补强**（规格 `02-证明路线/02-定理清单.md` T1A.9）
> 本文件做什么
> 规格 T1A.9：
> > `FCA 基本定理：概念格是完备格；形式概念是 Galois 连接的不动点`

**核心定义**（3 个）：

- `sInfConcept` (L31)
- `sSupConcept` (L59)
- `conceptLatticeCompleteLattice` (L109)

**定理**：共 14 条，其中名字含主定理特征的 1 条：

- `T1A9_conceptLattice_complete_substantive` (L131)

---

## `FrameBridge`

**模块自述**：

> §2  把 `Model`/`Obs` 接到本项目的 `Frame`（突破的具体化）
> **背景**：`Fate/Counterfactual.lean` 的突破（商上单值化）是在**抽象 `Model`** 上证的：
> ```lean
> structure Model where
> SCM : Type*      -- 结构方程集
> CF  : Type*      -- 反事实预测空间

**核心定义**（2 个）：

- `frameModel` (L18)
- `bridgeFiber` (L26)

**定理**：共 4 条，其中名字含主定理特征的 1 条：

- `bridge_quot_subsingleton_iff` (L39)

---

## `GaloisEmbedding`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.GaloisEmbedding
> 阶段：**阶段 1A/1B —— 对 `Fate.FCA` 中导出算子对的判定与证明**
> 本文件回答的问题
> 规格与裁决链中反复出现一个悬而未决的技术问题：
> > `polarUp` / `polarDown` 这对导出算子，**是否**诱导一个

**定理**：共 14 条，其中名字含主定理特征的 5 条：

- `polarUp_polarDown_eq_self_iff_injective` (L31)
- `polarUp_polarDown_eq_self_iff_all_isIntent` (L47)
- `not_galoisInsertion_of_exists_not_isIntent` (L52)
- `not_forall_galoisInsertion` (L82)
- `polarUp_subset_iff_subset_polarDown_on_closed` (L127)

---

## `GazeAlgebraConsumer`

**模块自述**：

> 命运理论 · GazeAlgebra 接入主链（叶子接线 4）
> 本文件做什么 / 诚实边界
> `Fate.GazeAlgebra`（22 定理）此前是**叶子模块**（零消费者）。
> 它在一个**自足副本** `GazeAlgebra.G` 上研究「三种目光的代数结构」，
> 并在 §7 只给出 `G ≃ Fin 3` 的**类型层双射**，
> **明确不 import `Fate.Classification`**（源文件 §7 原话：

**核心定义**（2 个）：

- `equivG` (L34)
- `negG` (L76)

**定理**：共 8 条，其中名字含主定理特征的 1 条：

- `isElement_iff_bot` (L66)

---

## `KernelQuotient`

**模块自述**：

> §10  统一框架：**核–商理论**（`KernelQuotient`）
> ## 缘起
> 本项目在三个互相独立的位置**各自**重建了同一个结构：
> | 文件 | 载体 | 映射 | 「核」 | 「商」 |
> |---|---|---|---|---|
> | `Fate/Counterfactual.lean` | `Model.SCM` | `Obs` | `cfSetoid = ker Obs` | `cfQuotient F` |

**核心定义**（8 个）：

- `descend` (L33)
- `quotientEquivRange` (L57)
- `Collapse` (L128)
- `Faithful` (L131)
- `MiddleZone` (L134)
- `faithfulEquivOfSubtype` (L165)
- `kappa` (L220)
- `Compatible` (L284)

**定理**：共 29 条，其中名字含主定理特征的 11 条：

- `quot_eq_iff` (L41)
- `descendBy_injective_iff` (L83)
- `descendOnSubtype_injective_iff` (L102)
- `collapse_iff_subsingleton` (L146)
- `faithful_iff_quot_subsingleton_quot` (L179)
- `descendBy_iff` (L195)
- `kappa_mono_of_comp` (L223)
- `compatible_iff_le_kernel` (L291)
- `kernel_is_coarsest_unique` (L301)
- `obs_constant_iff_kernel_top` (L398)
- …另 1 条

---

## `KernelQuotientCategorical`

**模块自述**：

> §12  核–商理论的**范畴化**（`KernelQuotientCategorical`）
> ## 缘起
> `Fate/KernelQuotient.lean`（命名空间 `Fate.KernelQuotientTheory`）把项目里
> 三处独立重建的结构统一为**一个** `Set`-层理论：对**任意** `f : A → B`，
> 核 `ker f`、商 `A/ker f`、第一同构 `A/ker f ≃ range f`、三情形穷尽、
> 核族的完备子格性质。

**核心定义**（9 个）：

- `kernelPairLift` (L63)
- `CatCollapse` (L134)
- `CatFaithful` (L138)
- `CatMiddleZone` (L142)
- `linearMap_quotKerEquivRange` (L239)
- `moduleCat_kernelIsoKer` (L251)
- `moduleCat_imageIsoRange` (L256)
- `group_quotientKerEquivRange` (L267)
- `ring_quotientKerEquivRange` (L277)

**定理**：共 24 条，其中名字含主定理特征的 10 条：

- `kernelPair_iff_isPullback` (L48)
- `kernelPair_id_of_mono` (L82)
- `catCollapse_iff` (L155)
- `subobject_le_iff_exists_mono` (L181)
- `typesKernelPair_iff_kernel` (L199)
- `types_kernel_le_iff` (L204)
- `types_epi_iff_surjective` (L209)
- `types_mono_iff_injective` (L214)
- `types_quotient_equiv_range_agree` (L219)
- `linearMap_ker_eq_bot_iff` (L245)

---

## `KernelQuotientExtra`

**模块自述**：

> §13  **核-商理论的补充定理**（并入统一框架）
> **背景**：`Fate/KernelQuotient.lean`（统一框架主体，27 条定理）与
> 此前的 `Fate/KernelQuotientCore.lean`（11 条）**同命名空间、部分重名**，
> 无法同时进构建（实测：`environment already contains 'Fate.KernelQuotient.Faithful'`）。
> **处置**：以 `KernelQuotient.lean` 为**唯一权威主体**（更完整），
> 本文件把 `KernelQuotientCore` 中**独有**的定理**并入同一命名空间**，

**定理**：共 4 条，其中名字含主定理特征的 2 条：

- `kernel_le_iff` (L26)
- `kernel_joint_iff` (L33)

---

## `KernelQuotientRecovery`

**模块自述**：

> §11  **三套结构的回收**：证明它们都是一般理论的**特例**
> **动机**：`Fate/KernelQuotientCore.lean` 给出了「映射 → 核 → 核商」的一般理论。
> 本节**实际证明**项目里三套独立结构**都是它的实例** ——
> **不是口头声称，而是可编译的 `example` 层面的回收**。
> | 来源 | 一般理论的哪个实例 |
> |---|---|

**定理**：共 8 条


---

## `MVFCAClosure`

**模块自述**：

> §0  MVFCA 闭包的补全：`cl` 幂等 + `ClosureOperator` 实例 + 闭集交封闭
> ## 背景
> `Fate/MVFCAPositive.lean` 已定义模式结构与标准闭包：
> ```lean
> structure PatStruct (G) (L) [CompleteLattice L] where desc : G → L
> def up   (K) (A : Set G) : L     := ⨅ g ∈ A, K.desc g

**核心定义**（1 个）：

- `closureOperator` (L51)

**定理**：共 7 条，其中名字含主定理特征的 2 条：

- `cl_mono` (L40)
- `isClosed_iff_closureOperator` (L58)

---

## `MVFCAFinset`

**模块自述**：

> MVFCA · **`minClosed` / `attrClosure` 的 Finset 版（可枚举算法）**
> COMPLEX-1 §5 第 9、10 条：
> * 第 10 条：`minClosed`（`Fate/AlphaMVFCA.lean`，`K.cl {g}`，`Set` 层）
> 只有「`Set` 层 ⋂₀ / `down` 定义」，**没有 Finset 计算版**；
> * 第 9 条：`attrClosure`（`Fate/FcaToRuleTerm.lean`，`∃` 定义）同理。
> 本模块在 `[Fintype G]` + `[DecidableEq L]` 下给出**只需枚举 `G` 全部元素**

**核心定义**（2 个）：

- `minClosedFinset` (L42)
- `attrClosureFinset` (L101)

**定理**：共 12 条，其中名字含主定理特征的 1 条：

- `mem_minClosed_iff` (L34)

---

## `Minimality`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Minimality
> 阶段：**阶段 1B —— DG 基的最小性**（规格 T1A.10 的「最小」一半）
> 本文件做什么
> 规格 `02-证明路线/01-路线图.md` **T1A.10**：
> > `DG 基是最小完备蕴含基`｜前件：**形式背景有限**｜类别 ①

**核心定义**（5 个）：

- `IsComplete` (L24)
- `Lemma348` (L38)
- `PseudoIntentClosureInjective` (L45)
- `coverRule` (L68)
- `IsNonRedundantComplete` (L151)

**定理**：共 10 条，其中名字含主定理特征的 1 条：

- `dgbasis_isComplete` (L28)

---

## `PairingAlphaBridge`

**模块自述**：

> §P3-①  配对层 → FCA 数据的桥（**对象集紧锁版**）
> ## 与 `Fate/PairingToAlphaData.lean` 的关系（必读）
> `Fate/PairingToAlphaData.lean` 已给出一个 `pairingToAlphaData`，
> 但它的签名里有**未被使用的参数** `P : Pairing ι` 与 `γ : ι → X.Carrier`
> （编译期 `linter.unusedVariables` 直接告警），定义体是 `obs := fun t => attr t.1`。
> **⟹ 那个构造与配对无关**：`P`、`γ` 进不去定义体，

**核心定义**（2 个）：

- `transInst` (L19)
- `transInst_mono` (L59)

**定理**：共 9 条，其中名字含主定理特征的 1 条：

- `transitions_mono` (L38)

---

## `PairingToAlphaData`

**模块自述**：

> 规则核心链 · 断点① · **配对层 → FCA 数据**
> ## 本模块做什么
> 把 `Pairing`（配对策略，策略 A/B/C 均可）与一条轨迹 `γ` 产生的**转移对集合**
> `Pairing.transitions P γ : Set (Transition X)`，变成 FCA 可以吃的 `AlphaData`。
> ## 关键事实（实测原文）
> ```lean

**核心定义**（4 个）：

- `transInstSpace` (L19)
- `pairingToAlphaData` (L25)
- `pairingToAlphaDataPost` (L35)
- `pairingToAlphaDataBoth` (L44)

**定理**：共 3 条


---

## `Rule13Genuine`

**模块自述**：

> `Fate/Rule13Genuine` —— **缺口 3（续）：规则 1 与规则 3 的真语义版本**
> （第 249 轮）
> ## ⚠⚠ 一、要修的东西
> 第 247 轮 J1 审核判定：
> | 旧定理 | 文件 | 证明体 | 判定 |
> |---|---|---|---|

**核心定义**（5 个）：

- `XIndependent` (L21)
- `MassOne` (L25)
- `EffNull` (L127)
- `M1` (L158)
- `MC` (L196)

**定理**：共 18 条，其中名字含主定理特征的 3 条：

- `main_zero` (L72)
- `main_one` (L83)
- `XIndependent_not_necessary` (L181)

---

## `Rule13GenuineConsumer`

**模块自述**：

> `Fate/Rule13GenuineConsumer` —— **`Rule13Genuine` 的消费层**
> （P5 并行任务，第 740 轮）
> ## 一、上游模块（实测声明，`Fate/Rule13Genuine.lean`，471 行）
> | 命名空间 | 声明 | 类型 |
> |---|---|---|
> | `R249.Exog` | `XIndependent` | `def`（外生层前提，规则 1）|

**核心定义**（2 个）：

- `MZ` (L58)
- `rebase` (L118)

**定理**：共 22 条


---

## `Rule1Semantic`

**模块自述**：

> `Fate/_r242_G3` —— **缺口 3：do-calculus 规则 1 的语义版本**（第 242 轮 · G3）
> ## 文献（N1）
> **Pearl, *Causality* (2nd ed.), Theorem 3.4.1（规则 1）**：
> > `P(y | do(x), z, w) = P(y | x, z, w)`  若 `Y ⊥_d X | Z, W` in `G_{\overline{X}}`
> ## 本任务的定位
> `Fate/DoCalculusRules.lean` 只有**图的子集关系**（`rule2Graph ⊆ rule1Graph` 等）——

**核心定义**（5 个）：

- `margX` (L26)
- `NoConfounding` (L37)
- `NoUDependence` (L42)
- `M1` (L110)
- `M2` (L258)

**定理**：共 29 条，其中名字含主定理特征的 3 条：

- `noConfounding_iff_condProb_eq_doLaw_guarded` (L70)
- `T35_rule1_boundary` (L102)
- `condY_eq_zero_iff_doLaw_eq_zero` (L401)

---

## `Rule23Semantic`

**模块自述**：

> ⚠⚠ **第 247 轮降级声明（J1 批量审核发现）**
> **⚠ 本模块的「语义定理」实际上**前提就是结论**（P3 级）。**
> ## J1 的实测
> | 定理 | 证明体 | 判定 |
> |---|---|---|
> | **`rule2_semantic`** | **`fun x z y => h x z y`** | ❌ **前提直接就是结论** |

**核心定义**（16 个）：

- `zOf` (L30)
- `xOf` (L33)
- `joint3` (L36)
- `doLaw2` (L44)
- `doLawX` (L49)
- `zMass` (L56)
- `doLawXCond` (L61)
- `doLawXOnly` (L67)
- `obsY` (L73)
- `Rule2Condition` (L101)
- `Rule3Condition` (L106)
- `chain` (L139)
- …另 4 个

**定理**：共 31 条，其中名字含主定理特征的 2 条：

- `Rule2Condition_iff` (L125)
- `Rule3Condition_iff` (L131)

---

## `RuleActivationClosureOp`

**模块自述**：

> §0  激活闭包的抽象化：`ClosureOperator` 实例
> ## 背景
> `Fate/RuleActivation.lean` 已定义：
> ```lean
> def Coherent (a : Activation R) (T : Set R) : Prop :=
> a.init ⊆ T ∧ ∀ r ∈ T, ∀ s, a.dep r s → s ∈ T

**核心定义**（3 个）：

- `closureOp` (L14)
- `closureOperator` (L68)
- `closedSets` (L77)

**定理**：共 22 条，其中名字含主定理特征的 4 条：

- `closureOp_mono` (L29)
- `isClosed_iff_mem_closedSets` (L85)
- `mem_readSet_closure_exists_chain` (L136)
- `mem_closedSets_iff_ancestralSet_eq` (L248)

---

## `RuleActivationClosureOpConsumer`

**模块自述**：

> `Fate/RuleActivationClosureOpConsumer` —— **`RuleActivationClosureOp` 的消费层**
> ## 一、上游实测声明（`Fate/RuleActivationClosureOp.lean`，129 行）
> | 声明 | 类型 |
> |---|---|
> | `RuleActivation.closureOp (dep) (suppressed) (s)` | `def`（固定 `dep`/`suppressed`，变 `init`）|
> | `RuleActivation.closureOp_extensive` | `theorem` |

**定理**：共 12 条，其中名字含主定理特征的 1 条：

- `closedSets_iff_coherent` (L79)

---

## `RuleDrivesEndToEnd`

**模块自述**：

> P0-2/P0-3 · 把 `LawRule` 抽出的 `Step` **真正接进** `WorldModel` / `EndToEnd` 主链
> ## 背景（实测，非猜测）
> ### `WorldModel` 的完整字段清单（`Fate/WorldModel.lean:296`，实测）
> ```
> structure WorldModel where
> frame : Frame

**核心定义**（1 个）：

- `ruleWorldModel` (L27)

**定理**：共 19 条，其中名字含主定理特征的 1 条：

- `ruleWorldModel_endToEnd_fixed_iff` (L281)

---

## `RuleEntersWorldModel`

**模块自述**：

> 规则核心链 · P0-2 / P0-3 · **规则驱动的整条世界模型轨迹**
> ## 本模块做什么
> 把 `LawRule` 在 `IsDirac` 档抽出的 `Step` 装进 `WorldSimulator`，
> 并证明 `trajGen`（世界模型的轨迹生成器）在它上面生成的轨迹
> **就是** `LawRule` 自己的轨迹（`trajOfRichLaw`）。
> ## 关键定义（实测原文）

**核心定义**（14 个）：

- `ctxOfRich` (L23)
- `ruleSimulator` (L32)
- `wTheta` (L151)
- `wX` (L157)
- `wU` (L164)
- `wAct` (L170)
- `wN` (L176)
- `wC` (L181)
- `wFrame` (L185)
- `wZero` (L208)
- `wOne` (L211)
- `lawToZero` (L214)
- …另 2 个

**定理**：共 14 条，其中名字含主定理特征的 1 条：

- `trajGen_rule_unique` (L134)

---

## `RuleExecDemo`

**模块自述**：

> 规则可执行引擎 · **`#eval` 演示**（P1-H1）
> ## 为什么有这个文件
> `Fate/RuleExec.lean` 是全仓**唯一**能把规则跑成 `Bool` 的纯可执行引擎
> （`Term.check : Term → EnvQ → Bool`），并且已有
> `Term.check_iff_holds` / `run_iff_holds` 把它钉到语义 `RuleTerm.holds` 上。
> 但在 CHAIN-4 审计时它 **0 处 `#eval`**，且仅 `TermSize.lean` /

**核心定义**（7 个）：

- `env1` (L16)
- `env2` (L19)
- `env0` (L22)
- `tA` (L25)
- `tB` (L28)
- `tC` (L31)
- `tD` (L34)

**定理**：共 3 条


---

## `RuleMainChainConsumer`

**模块自述**：

> P0-G1 · 把规则桥接进主链：`ruleWorldModelWithRules` 的**第一个外部消费者**
> ## 背景（CHAIN-2 审计，实测计数）
> * `Fate/RuleSimConsistency.lean` 里的 `ruleWorldModelWithRules` **真的**把
> `rules` 字段接上了外生规律 `R`（其核逐点等于 `R c x`，见 `ruleOfLaw_kernel_mem`）。
> * 但审计发现：`ruleWorldModelWithRules` 在 `EndToEnd.lean` 里出现 **0** 次，
> 在 `RuleSimConsistency.lean` 之外的**任何**文件里出现 **0** 次。

**定理**：共 6 条


---

## `RuleReadSet`

**模块自述**：

> `Fate/RuleReadSet` —— **规则读集与规则间依赖**（含激活闭包）
> ## 背景（作者澄清）
> 世界模型里规则是 **「全参与 + 按需激活」**，**不是**从集合里挑一条。
> 机制：**开始全部激活 → 数据进来部分不激活 → 但被依赖的规则立刻重新激活
> （闭包传播）**。
> 规则间依赖有两个来源：

**核心定义**（8 个）：

- `ReadsAt` (L28)
- `readSet` (L32)
- `DependsOn` (L44)
- `DeterminesAt` (L86)
- `detSet` (L90)
- `ruleDep` (L120)
- `ruleDepWith` (L150)
- `closure` (L167)

**定理**：共 36 条，其中名字含主定理特征的 11 条：

- `mem_readSet_iff` (L36)
- `dependsOn_mono` (L48)
- `mem_detSet_iff` (L94)
- `ruleDep_iff` (L124)
- `ruleDep_iff_ne_empty` (L129)
- `ruleDep_mono_det` (L134)
- `ruleDep_mono_read` (L139)
- `ruleDep_imp_inter` (L144)
- `closure_mono_I` (L208)
- `closure_mono_dep` (L240)
- …另 1 条

---

## `RuleReadSetWiringConsumer`

**模块自述**：

> `Fate/RuleReadSetWiringConsumer` —— **消费 `RuleReadSetWiring` 的核心结论**
> ## (a) 目标模块 `RuleReadSetWiring` 的实测声明清单
> `grep -nE "^(theorem|def|noncomputable def|instance|lemma|abbrev|structure|inductive)"
> Fate/RuleReadSetWiring.lean` **实测 29 条**（`grep -cE "^theorem"` = 24，
> `def` 4，`structure` 1；⚠ 注：`RuleSetWithDeps` 命名空间内的 4 条
> `theorem` 在源文件中**无缩进**，故全部计入 24）：

**定理**：共 6 条，其中名字含主定理特征的 2 条：

- `wmc_ruleDepWith_iff_manual` (L28)
- `wmc_closed_iff_manual_closed` (L86)

---

## `RuleRelaxation`

**模块自述**：

> P4 · 乙路线 · **规则与机制的误差逼近：格序形式**
> ## 本模块做什么
> 总纲 §4 P4 要求「对集合档规则给出『预测质量』度量」，并登记根本障碍：
> > `Measure Y` 上**没有自然度量** ⟹ `Set (Measure Y)` 上也没有
> > ⟹ `‖R − f‖` **无法定义**，除非引入 Wasserstein 距离
> > （要求 `Y` 是 Polish 空间）。

**核心定义**（1 个）：

- `IsRelaxationOf` (L18)

**定理**：共 10 条，其中名字含主定理特征的 1 条：

- `isRelaxationOf_mono` (L39)

---

## `RuleSimConsistency`

**模块自述**：

> T12 · `WorldModel.rules` 与其 `simulator` 的**一致性定理**
> ## 背景（实测，非猜测）
> 外部规划（命运项目·执行规划.md v2）§1.3 问题 1 指出：
> > `WorldModel.rules` 字段是占位符。两个独立字段，结构不保证关联。
> > `ruleWorldModel` 里 `rules` 填占位的 dirac 规则，
> > `simulator` 填真正的规则驱动步进。

**核心定义**（2 个）：

- `ruleOfLaw` (L25)
- `ruleWorldModelWithRules` (L57)

**定理**：共 14 条


---

## `RuleSyntaxOps`

**模块自述**：

> 规则核心链 · **IR 四算子的语法层对应**（乙-2 第 1 件）
> ## 本模块做什么
> `规则层类型学基础.md` §五 给出四算子：
> | 算子 | 语义 | 本模块的语法层实现 |
> |---|---|---|
> | **`α`（抽象）** | 从实例产生规则 | `alphaFrom`（从具体环境 `e` 造出 `xᵢ = eᵢ` 的合取） |

**核心定义**（6 个）：

- `trueTerm` (L21)
- `generalize` (L30)
- `loosen` (L45)
- `refine` (L70)
- `compose` (L84)
- `alphaFrom` (L106)

**定理**：共 10 条，其中名字含主定理特征的 3 条：

- `holds_refine_iff` (L77)
- `holds_compose_iff` (L87)
- `holds_alphaFrom_iff` (L112)

---

## `Satisfiability`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.Satisfiability
> 阶段：**阶段 1C —— 规则组合的完备性（交非空 / 可满足性）**
> 本文件回答的问题
> 给定一族属性蕴含规则 $\Sigma\subseteq\mathcal{P}(M_{\mathrm{FCA}})\times
> \mathcal{P}(M_{\mathrm{FCA}})$，问：

**核心定义**（4 个）：

- `Sat` (L25)
- `Entails` (L56)
- `cl` (L60)
- `SatAvoid` (L185)

**定理**：共 30 条，其中名字含主定理特征的 8 条：

- `sat_iff_models_nonempty` (L29)
- `entails_iff_subset_cl` (L87)
- `synClosureOne_models_iff` (L105)
- `dgbasis_isModelOf_iff_closed` (L172)
- `satAvoid_iff` (L189)
- `cl_mono` (L230)
- `entails_mono` (L241)
- `satAvoid_univ_iff` (L269)

---

## `T112Candidates`

**模块自述**：

> `Fate/T112Candidates` —— **T1.12 · 步骤 1–2：五个候选命题的探针测试**
> # 本文件的用途
> 对 5 个「看似 FCA 特有」的候选命题，**逐条**做**可机器验证**的判定：
> | 判定 | 机器形式 |
> |---|---|
> | **不是 FCA 特有** | 该命题对**任意** `ClosureOperator`（或至少对 `Unary` 单底集情形）**逐字成立**。直接给出证明项。 |

**定理**：共 10 条，其中名字含主定理特征的 2 条：

- `fix_completeLattice` (L14)
- `isExtent_iff_uClosure_fix` (L98)

---

## `T112Exactly`

**模块自述**：

> `Fate/T112Exactly` —— **T1.12 · 第 5 次尝试：把问题彻底答完**
> # 本文件回答
> > **「FCA 到底有没有一般闭包算子没有的定理？」**
> ## §1 结论（先说）
> > **没有。而且比「没有」更强：FCA 与「幂集上的闭包算子」是**外延相同**的（coextensive）。**
> 这不是「前几次尝试没找到」，而是**一个可以机器验证的完全刻画**：

**核心定义**（1 个）：

- `cloRel` (L14)

**定理**：共 16 条，其中名字含主定理特征的 2 条：

- `isIntent_iff_closure_fix` (L143)
- `mk_eq_iff_closure_eq` (L162)

---

## `T112FCAConnection`

**模块自述**：

> `Fate/T112FCAConnection` —— **T1.12 T1.11 与 FCA 的衔接**（**第 223 轮**）
> ## 清单原文（T1.12）
> > **T1.12 与 FCA 的衔接（本框架专属）**：
> > 若 `∼_ℰ` 取为「在属性集 `I` 下具有相同属性集」，
> > 则 `ℰ/∼_ℰ` 与 `𝕂` 的对象概念的集合之间存在**双射**。
> ## ⭐ 这条为何是「本框架专属」

**核心定义**（5 个）：

- `attrsOf` (L12)
- `sameAttrs` (L16)
- `attrsSetoid` (L24)
- `quotClassAttrs` (L36)
- `closure` (L58)

**定理**：共 7 条，其中名字含主定理特征的 2 条：

- `sameAttrs_equivalence` (L20)
- `sameAttrs_iff` (L31)

---

## `T112FCAPolar`

**模块自述**：

> ⚠ **第 247 轮标注（J1 批量审核）：**本模块是纯格论，非概率****
> **J1 的实测**：6 条定理中**概率相关性 = 0**。
> ## ✅ 有内容的部分
> - `id_not_doublePolar_counterexample`：`by_contra`，`Unit` 上的真反例
> - `upperPolar_univ_ne_univ`
> ## ⚠ 规模问题

**定理**：共 6 条，其中名字含主定理特征的 1 条：

- `polarUp_eq_iff_isIntent` (L23)

---

## `T112FCASpecific`

**模块自述**：

> `Fate/T112FCASpecific` —— 第 247 轮：**真正 FCA 特有**的定理（含诚实标注）
> ## 任务书三条
> | # | 任务 | 结论 |
> |---|---|---|
> | 1 | ⭐⭐⭐ 概念外延 ↔ 概念内涵 是**反序同构** | ✅ 已证，**FCA 特有**（需两端伴随） |
> | 2 | ⭐⭐⭐ 双极闭包秩 ≤ 2（四次极 = 二次极） | ✅ 已证，但 ⚠ **非 FCA 特有** |

**核心定义**（18 个）：

- `extentIntentAnti` (L75)
- `f3` (L99)
- `cl3` (L132)
- `a0` (L256)
- `a1` (L388)
- `shift4` (L466)
- `zA` (L482)
- `oA` (L484)
- `zC` (L486)
- `oC` (L488)
- `KA` (L498)
- `KC` (L504)
- …另 6 个

**定理**：共 91 条，其中名字含主定理特征的 2 条：

- `cl3_isClosed_iff` (L135)
- `phi_le_iff` (L745)

---

## `T112FCASpecific2`

**模块自述**：

> `Fate/T112FCASpecific2` —— **T1.12 · 步骤 3：穿过探针的 FCA 特有定理**
> # 前言：本文件的定理**全部是通过探针筛出来的**
> 5 个候选（见 `Fate/T112Candidates`）**全部**被判为「非 FCA 特有」。
> 本文件的 3 条定理是**换角度重新找**的：它们不是「FCA 的漂亮性质」，
> 而是**陈述本身必须两个底集**的命题。
> | # | 定理 | 为什么需要两个底集 | 分离探针 |

**核心定义**（1 个）：

- `conceptSwapEquiv` (L96)

**定理**：共 14 条，其中名字含主定理特征的 5 条：

- `polarUp_iff_adjoint_of_antitone` (L30)
- `polarDown_iff_adjoint_of_antitone` (L53)
- `unary_adjoint_not_unique` (L82)
- `conceptSwapEquiv_invol` (L110)
- `isExtent_iff_mem_range_polarDown` (L157)

---

## `T112FCATheorems`

**模块自述**：

> `Fate/T112FCATheorems` —— **T1.12 · 第 4 次尝试：经判据筛选的真 FCA 特有定理**
> # 本文件回答
> > **「FCA 有没有一般闭包算子没有的定理？」**
> ## §0 判据（本轮唯一使用，可机器检查）
> | 判据 | 内容 |
> |---|---|

**核心定义**（2 个）：

- `SinglePoint` (L15)
- `KNoAttr` (L137)

**定理**：共 10 条


---

## `T112PairProbe`

**模块自述**：

> `Fate/T112PairProbe` —— **T1.12 · 步骤 2 的「两个底集」探针**
> # 本文件做什么
> 前面 5 个候选都被 `Fate/T112Candidates` 的探针判为「非 FCA 特有」。
> 这个文件换一个角度：**不猜命题，而是把「两个底集」当成一个结构来测**。
> ## 核心观察（本文件 §1）
> > **FCA = `setPVar` 上的两个闭包算子的组合**，

**核心定义**（3 个）：

- `cObj` (L16)
- `cAttr` (L19)
- `fixEquiv` (L25)

**定理**：共 3 条


---

## `T112SecondQuotient`

**模块自述**：

> `Fate/T112SecondQuotient` —— **T1.12 的「二次商」**
> # 🔴 降级声明（C4 审核判定 · **本文件整体降级**）
> ## C4 审核的判定（原文）
> > **「`T1.12` 就是 `Quotient.lift` + `Quotient.sound/exact` 的机械组合。
> > 探针实测：对**任意** `ClosureOperator α` 原样成立，完全不涉及 FCA。」**
> ## 本文件对此判定的**接受**与**形式化确认**

**核心定义**（14 个）：

- `closureOp` (L17)
- `attrsEquiv` (L48)
- `attrsEquivSetoid` (L56)
- `quotEquivIsClosed` (L81)
- `conceptOfClosure` (L109)
- `t112_bijection` (L118)
- `closureObj` (L174)
- `objsEquiv` (L189)
- `objsEquivSetoid` (L197)
- `conceptOfClosureObj` (L207)
- `t112_bijection_extent` (L224)
- `t112_bijection_closeds` (L273)
- …另 2 个

**定理**：共 52 条，其中名字含主定理特征的 14 条：

- `isClosed_iff_closure_eq` (L31)
- `attrsEquiv_equivalence` (L52)
- `attrsEquivSetoid_r` (L61)
- `attrsEquiv_self_closure` (L66)
- `mk_attrsEquiv` (L71)
- `t112_injective_iff` (L156)
- `objsEquiv_equivalence` (L193)
- `objsEquiv_self_closure` (L202)
- `exists_closed_rep` (L264)
- `closure_mono_apply` (L411)
- …另 4 条

---

## `T112UnaryClosure`

**模块自述**：

> `Fate/T112UnaryClosure` —— **T1.12 任务 · 步骤 2 探针公用件**
> # 本文件给「一般闭包算子」这一侧提供一个**统一的可陈述框架**
> ## 背景（为什么要这个文件）
> 前面几轮失败的模式是：把「一般闭包算子的结论」当成「FCA 特有」。
> 本轮把「是否 FCA 特有」化归为一个**可判决的比较**：
> > 候选命题 `P` 若能在 **`Unary` 框架**中陈述，则它 **不是** FCA 特有；

**核心定义**（1 个）：

- `uClosure` (L12)

**定理**：共 4 条，其中名字含主定理特征的 2 条：

- `isExtent_iff_isIntent_of_symm` (L32)
- `isExtent_iff_lowerPolar_lowerPolar` (L45)

---

## `T35Rule1NoConfounding`

**模块自述**：

> `Fate/T35Rule1NoConfounding` —— **反例登记：草稿的第 242 轮 G3 命题为假**
> ## 0. 本文件是什么
> 第 242 轮 G3 代理产出了一份 218 行的草稿，标题为
> 「**do-calculus 规则 1 的语义版本**（T3.5 的逆命题：
> **无混杂 ⟹ 观测律 = 干预律**）」。
> **⚠ 本文件是那份草稿的「反例登记」，不是它的修复版。**

**核心定义**（3 个）：

- `NoConfoundingDraft` (L12)
- `MBad` (L35)
- `eBad` (L42)

**定理**：共 9 条，其中名字含主定理特征的 1 条：

- `draft_NoConfounding_iff` (L26)

---

## `T35Rule1Split`

**模块自述**：

> `Fate/T35Rule1Split` —— **缺口 3：do-calculus 规则 1 的语义版本**
> （**任务书原义的外生分解形式**：`X` 与 `Y` 用**不同的外生分量**）
> ## 0. 任务书要求
> > **缺口 3**：在「**无混杂**」条件下证明
> > `∀ x, doLaw M x = condY M x`，
> > 该条件表述为「**`Y` 的方程不使用 `X` 的方程所用的那个外生分量**」。

**核心定义**（10 个）：

- `NC` (L14)
- `NUD` (L18)
- `XReadsOnlyUx` (L24)
- `YReadsOnlyUy` (L29)
- `SplitNoConfounding` (L35)
- `SeparablePU` (L40)
- `FullNoConfounding` (L47)
- `eMNC` (L169)
- `MNC` (L172)
- `MBad` (L272)

**定理**：共 32 条


---

## `T35Rule1SplitConsumer`

**模块自述**：

> `Fate/T35Rule1SplitConsumer` —— `T35Rule1Split` 的**消费方**
> ## 0. 上游模块实测（`Fate/T35Rule1Split.lean`，657 行）
> `grep -nE "^(theorem|def|noncomputable def|instance)"` 实测 **37 条声明**
> （`namespace Fate.T35Rule1Split`，import `Fate.SCMSemantics`、
> `Fate.Rule1Semantic`）：
> | 类别 | 声明 |

**定理**：共 10 条，其中名字含主定理特征的 3 条：

- `NC_imp_L2_family_eq` (L21)
- `NC_imp_L2_do_cancel` (L43)
- `literal_rule1_iff_marginal_one` (L58)

---

## `T611Full`

**模块自述**：

> T6.11 —— DG 基的「完备且不冗余」表示 / ARM 阈值下的不完备性
> ## 规格原文（`02-证明路线/02-定理清单.md` L252）
> > **T6.11**  DG 基给出**完备且不冗余**表示；ARM 在任一阈值下
> > **不保证**穷尽（「阈值候选集漏掉某条成立的蕴含」）。
> > 类别 `[条件可证]`（后半 `[可证]`）；依赖 T1.8 / T1.9 / T1.10。
> ## 本文件的三处如实修正（陈述缺陷）

**核心定义**（3 个）：

- `IsStrongNonRedundant` (L82)
- `exCtx` (L104)
- `armRulesSup` (L252)

**定理**：共 29 条，其中名字含主定理特征的 11 条：

- `Models_iff` (L17)
- `modelsSound_empty` (L21)
- `weakComplete_empty` (L35)
- `isComplete_empty_imp_all_closed` (L40)
- `t611_DG_complete` (L53)
- `t611_DG_complete_nonredundant` (L67)
- `dgbasis_represents_iff` (L72)
- `strongImpNonRedundant` (L87)
- `nonRedundantImpStrong` (L91)
- `t611_DG_complete_strongNonRedundant` (L95)
- …另 1 条

---

## `T611FullConsumer`

**模块自述**：

> 消费方：T611Full 的消费定理（DG 基完备/不冗余 + ARM 不完备）
> 本文件**只新增**，不修改任何已有模块。它消费 `Fate.T611Full` 的核心结论：
> | T611Full 的结论 | 本文件的消费方式 |
> |---|---|
> | `dgbasis_represents_iff` | §2 把「完备」展开成逐点判据，用于反证 |
> | `t611_DG_models` / `t611_ARM_rule_false` | §3 分离「DG 可靠」与「ARM 不可靠」 |

**定理**：共 10 条，其中名字含主定理特征的 3 条：

- `notComplete_of_notClosed_model` (L14)
- `isClosedAttr_of_isComplete` (L23)
- `ex_dg_complete_nonredundant` (L61)

---

## `UpsilonIterConsumer`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.UpsilonIterConsumer`
> 阶段：**P5-甲（批 2）—— `Fate.UpsilonIteration` 的消费方**
> ## 0. 本文件只做一件事
> 把 `Fate/UpsilonIteration.lean` 的结论**接到下游**。**不修改**该模块一个字符。
> ## 1. 目标模块的实测声明（`grep -nE "^(theorem|def)" Fate/UpsilonIteration.lean`）

**定理**：共 4 条，其中名字含主定理特征的 3 条：

- `finite_bound_track_saturated_at_its_data` (L20)
- `tailed_bound_stabilizes` (L50)
- `two_tracks_tendsto_same_point` (L85)

---

## `UpsilonIteration`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.UpsilonIteration
> 阶段：**阶段 1B 补充 —— 「信息不断注入」作为 υ 的迭代**
> 本文件回答的问题
> 理论把（完善／更新）算子 υ 的作用写成**递推**：
> $R_{t+1}=\upsilon(R_t,\mathrm{Data}_t)$（规格定义 5.8，出处 03:460）

**核心定义**（4 个）：

- `upsilonIter` (L25)
- `cexUpsilon` (L235)
- `cexInj` (L266)
- `cexTrack` (L273)

**定理**：共 30 条，其中名字含主定理特征的 8 条：

- `upsilonIter_succ_eq_iff` (L61)
- `upsilonIter_mono` (L81)
- `upsilonIter_tendsto_of_eventually_static` (L126)
- `upsilonIter_limit_fixed` (L155)
- `upsilonIter_limit_unique` (L161)
- `upsilonIter_exists_eq_within` (L203)
- `cex_no_uniform_card_bound` (L300)
- `fca_upsilonIter_mono` (L367)

---

## `UpsilonIterationConsumer`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：`Fate.UpsilonIterationConsumer`
> 阶段：**P5-甲（批 1）—— `Fate.UpsilonIteration` 的消费方**
> 本文件做什么（一句话）
> `Fate.UpsilonIteration` 给出了「信息不断注入」下的 υ 迭代
> $x_{t+1}=\upsilon_{\mathrm{inj}(t)}(x_t)$，以及两条**互不替代**的收敛定理：

**定理**：共 7 条，其中名字含主定理特征的 1 条：

- `tracks_tendsto_zero_under_contracting` (L96)

---

## `UpsilonRefine`

**模块自述**：

> §0  `υ`（完善/收窄）的三重处理（作者裁决「三者并行」）
> ## 背景
> `Fate/LawRule.lean:139,142`：
> ```lean
> def generalize (R₁ R₂) (_h : ∀ c x, R₁ c x ⊆ R₂ c x) : LawRule C X Y := R₂
> def refine     (R₁ R₂) (_h : ∀ c x, R₂ c x ⊆ R₁ c x) : LawRule C X Y := R₂

**核心定义**（1 个）：

- `refine'` (L34)

**定理**：共 6 条


---

## `WiringFCAAlphaConsumer`

**模块自述**：

> 命运理论 · Lean 4 形式化实现
> 模块：Fate.WiringFCAAlphaConsumer
> 【甲-批4 / P5】`Fate.WiringFCAAlpha` 的下游消费者
> 本文件**只 `import Fate.WiringFCAAlpha`**，不改任何既有模块一行。
> 0. 目标模块实测声明清单（`grep -nE "^(theorem|def|noncomputable def|instance)"`）
> 共 30 条声明（23 条 `theorem` + 5 条 `def` + 2 条 `instance`），按命名空间分组：

**核心定义**（1 个）：

- `alphaReadAlpha` (L117)

**定理**：共 25 条，其中名字含主定理特征的 1 条：

- `alphaRead_partition_eq_iff` (L137)
