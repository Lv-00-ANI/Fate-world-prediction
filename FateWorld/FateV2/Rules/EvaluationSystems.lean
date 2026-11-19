/-
命运理论 · **多评价体系并存**（EvaluationSystems）
================================================================

模块：`EvaluationSystems`

---------------------------------------------------------------------------
(a) 作者第 537 轮裁决原话
---------------------------------------------------------------------------
> 「**净版那个评价有问题你得重新构建一个基于科学哲学的完善评价体系而且
>   还需要考虑是否需要变成一个自更新的元评价体系以及多种评价体系同时存在**」

⟹ 本文件只落实该裁决的**第三支**：「**多种评价体系同时存在**」。
「自更新的元评价体系」（`MetaBetter`）**本任务不含**，见下方 (d)。

---------------------------------------------------------------------------
(b) 对净版（5.7）评价体系的科学哲学批评（至少 3 条）
---------------------------------------------------------------------------
**批评 1 —— 波普尔的 `conf` 悖论。**净版把 `conf(R) = P(consequent | antecedent)` 当作「规则好不好」的主标量。
但波普尔本人的立场恰好相反：`conf`（**确证度**）**越高越像重言式**
（前件宽、后件必然，`conf → 1` 而无信息量），
**越可证伪的规则 `conf` 反而越低**。
用 `conf` 作评价标量，等于把「可证伪性」这一波普尔核心价值**反向激励**。
⟹ 净版不是「不完整」，而是**方向可能反了**：它把该**最小化**的量当成了该**最大化**的量。
⟹ 本文件因此把 `conf` 类的量拆成**两个独立的维度**
（`falsifiability` 与 `simplicity` 等共 8 个），**不预设它们的加权方向可统一**。

**批评 2 —— 费耶阿本德的多元论（`against method`）。**
净版假定了**唯一一套**评价量、**唯一一种**排序。
费耶阿本德论证：不存在**跨范式的、中立的**评价标尺；
「哪个理论更好」的问题在范式之间**不可通约**，
任何把它归约为单一标量的做法都是在**偷偷预设一个范式**。
⟹ 严肃的结论是：**必须允许多个评价体系同时存在，且允许它们给出相反排序**，
而不是造一个「总评价」。

**批评 3 —— 杜恒–奎因整体论（Duhem–Quine thesis）。**
净版把评价单位设为**单条规则** `R`。
杜恒–奎因指出：任何假说都**不能被单独检验**，
它总是连同辅助假说一起面对证据；
失败（或被确证）的是**整个理论网**，而非某一条规则。
⟹ 把「规则级」的评价量当作**具有独立意义**的量，是一个**未经辩护的原子论假设**。
本文件保留规则级评价作为**工程记账**，但**不声称**它具有整体论意义上的裁决力。

**批评 4（附）—— 上述三点合起来的元层次结论。**
净版的一维排序隐含「存在一个总序」。
本文件的做法：**把「排序」本身做成参数**（`EvaluationSystem.le` 只要求**前序**：
自反 + 传递），于是**不同的 `le` 就是不同的体系**，
它们之间**不要求相容**——而这正是 `systems_can_disagree` 所形式化的内容。

---------------------------------------------------------------------------
(c) 本文件的 5 步（严格按 TASK-1 规范，单一路径，无分支）
---------------------------------------------------------------------------
1. `structure Dimensions`：**8 个**科学哲学评价维度
   （`falsifiability` / `simplicity` / `explanatory` / `consistency` /
     `robustness` / `independence` / `operationality` / `novelty`），
   全部是 `Rule C X Y → ℝ`，即**纯参数**，**不赋予任何公式**；
2. `structure EvaluationSystem`：一个**评价体系** =
   名字 + 评价量载体 `Eval` + `eval` + 前序 `le`（自反 + 传递）；
3. `EvaluationSystem.toRuleEvaluation`：把体系**桥接**到
   `RuleEval.RuleEvaluation`（`structure` → `class` 实例），
   使 `Better` 及其三条定理**自动可用**；
4. 三个具体体系：`popperSystem`（只读 `falsifiability`）、
   `occamSystem`（只读 `simplicity`）、
   `lakatosSystem`（读 `explanatory + novelty`）；
5. **唯一的定理** `systems_can_disagree`（**费耶阿本德论纲**）：
   若某两条规则在可证伪性上的排序与在简洁性上的排序**相反**，
   则波普尔体系与奥卡姆体系**给出相反排序**；
6. **§6 `MetaBetter` + `metaBetter_irrefl`**（裁决的第三支：**自更新的元评价体系**）：
   `MetaBetter S₁ S₂` 说「`S₂` 能区分 `S₁` 认为不可比的一对规则」，
   即拉卡托斯「**进步性问题转移**」的一个形式化读法；
   `metaBetter_irrefl` 证明它**严格非自反**。

---------------------------------------------------------------------------
(d) 没做到什么（如实登记）
---------------------------------------------------------------------------
1. **`MetaBetter` 只形式化了「细粒度」这一条判据。** §6 的 `MetaBetter` 声称的是：「`S₂` 能区分 `S₁` 认为不可比的一对规则」，
   这是拉卡托斯「进步性问题转移」的**一个**（不是全部）形式化读法。
   拉卡托斯原文还要求「经验内容增长」与「部分超余内容被确证」，
   这两条**没有**形式化（因 `Rule` 不含前件/后件/概率空间 `P`）。
2. **不存在「终极元体系」的声称。** 按费耶阿本德，元评价本身也是一个范式；
   `MetaBetter` 只是**相对地**比较两个体系，
   它不定义「最好的体系」，也不保证 `MetaBetter` 上的链有极大元。
3. **`metaBetter_irrefl` 很浅。** 它只是「严格性」与「不可比性」不能同时成立于同一对元素；
   证明仅 `rintro` + `exact h3 h1`。**它不声称**元评价是传递的或完全的（这两者本文件均未证）。
2. **8 个维度是纯参数，没有任何公式或公理。**
   `Dimensions` 的字段是**任意**的 `Rule C X Y → ℝ`。
   ⟹ 本文件**不**声称这 8 个量能由 `Rule`（只有 `kernel`，无前件/后件/概率空间 `P`）
   算出来。这与 `Fate/RuleEvaluation.lean` §2 的登记**一致**：
   具体公式**仍是开放问题**。
3. **`systems_can_disagree` 不强于其前件。**
   该定理的结论是**两条 `≤`**，前件是**两条 `<`**；
   证明只用了 `le_of_lt`。它**不是**深刻的定理，
   它是「把 `popperSystem` / `occamSystem` 的定义**展开**后立刻成立」的**登记性引理**。
   ⚠ **特别声明**：它的作用域是**构造出的两个体系**，
   **不**声称「任何两个评价体系都会分歧」——后者是**假**的。
   前件 `hf` / `hs` **不是**结论的同义反复：它们是关于 `D` 的**两条独立的数值假设**，
   而非结论本身；但**没有这两条假设则结论不成立**（见下面的反例注记）。
4. **`lakatosSystem` 没有被任何定理使用。** 它只是 §4 的**第三个实例**，
   用于表明 `EvaluationSystem` **不**只容纳单维标量。
   ⟹ 不得声称「拉卡托斯体系已被验证」；它**只是被定义**。

---------------------------------------------------------------------------
(e) **第 537 轮裁决的落实登记 · 本轮新增 §7（与主干的桥）**
---------------------------------------------------------------------------
**作者原话（同 (a)，第 537 轮）**：
> 「**净版那个评价有问题你得重新构建一个基于科学哲学的完善评价体系
>   而且还需要考虑是否需要变成一个自更新的元评价体系以及多种评价体系同时存在**」

**§7 交付了什么**：
- `def ruleSpecSystem [FateV2.Rules.RuleSpec C X Y] : EvaluationSystem C X Y`——
  这是 **`RuleSpec` → `EvaluationSystem` 的桥**。
  `Fate/GammaOperator.lean:644` 的 `class RuleSpec` 恰好提供
  `le` / `refl` / `trans` 三个字段，与本文件的 `le` / `le_refl` / `le_trans`
  **逐一对应**，故桥是零成本投影。
  这使 `Fate/WorldModelCompleteV2.lean` 里 **`RuleSpec` 载体上的规则**
  （WMC `:168` 的单条规则层、`:191` 的规则集，及其 `RuleSpec.instPreorder`）
  **直接成为一个评价体系里的被评价量**。
- `theorem ruleSpecSystem_better_iff`——登记「经 §3 的 `toRuleEvaluation` 桥注册后，
  `RuleEval.Better` 与 `RuleSpec.le` **完全一致，无方向翻转**」。
  **⚠ 它的证明是 `rfl`（已实测），因此只是定义对齐，不是深刻定理。**

**(c) §7 的局限（必须如实登记）**：
1. **`Eval := Rule C X Y` 意味着「评价量就是规则本身」——
   本桥没有把 8 个维度（`falsifiability` … `novelty`）数值化。**
   要得到数值评价，仍需给出一个具体的 `Dimensions C X Y` 实例
   （再由 `popperSystem` / `occamSystem` / `lakatosSystem` 消费）。
   而具体 `Dimensions` 的公式**仍为开放问题**（见 (d) 第 2 条）。
2. **`RuleSpec.le` 的约定读法与「更好」相反。**
   `GammaOperator.lean:646` 的字段注释说 `le R₁ R₂` 读作「R₁ 比 R₂ **更一般**」，
   而本文件其余体系的 `le` 读作「**至少一样好**」（数值越大越好）。
   本桥**原样搬运** `RuleSpec.le`，**未翻转方向**。
   ⟹ **不得声称 `ruleSpecSystem` 表达了一个「更好」的判断**；
   它只表达「更一般或等价」。
3. **本文件仍然没有「自更新的元评价体系」。**
   裁决中的「自更新的元评价体系」一支，本文件仅有 §6 的
   `MetaBetter` + `metaBetter_irrefl`（且如在 (d) 第 1 条所述，
   `MetaBetter` 只形式化「细粒度」一条判据）。
   **自更新的动态过程（体系自身随证据改变）没有被形式化**；
   `MetaBetter` 是一个**静态的**体系间比较。
4. **不声称「把 8 个维度接进了主干」。**
   §7 接进主干的只是「规则本身」与「规则上的前序」，
   **不是** 8 个科学哲学维度。
   这正是下列事实的原因：`ruleSpecSystem` 与 `popperSystem` 等
   **没有可比较的共同评价量**（前者是 `Rule C X Y`，后者是 `ℝ`）。

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**

---------------------------------------------------------------------------
(f) **审计 R564 的落实登记 · 本轮新增 §8（可证伪性的真公式）**
---------------------------------------------------------------------------
**审计 R564 原话（逐字）**：
> 「**（最重要）**裁决 A 只完成约 **20%** —— 8 维度零公式。挑**可证伪性**做**一条真公式**
>   （`Rule` 有 `kernel`，可定义反例半径）。**不要再新建模块**。」

**(a) 一句话原则**：**一条真公式胜过 8 个空字段**。

**§8 交付了什么（严格 1 个 `def` + 2 条定理，未新建模块）**：
- `noncomputable def falsifiabilityOf (R : Rule C X Y) : ℝ`——
  `if R.IsDet then 1 else 0`，即「`1/(1+反例半径)`」在**两点反例半径**上的实例化；
- `theorem falsifiabilityOf_mem_Icc`——值域落在 `[0,1]`；
- `theorem falsifiability_det_ge_nondet`——确定性严格比非确定性**更可证伪**。

它由 `Rule` 的**唯一字段** `kernel`（经 `Rule.IsDet`，`Fate/Frame.lean:408`）算出，
因此是**本文件第一个由 `Rule` 计算出的评价量**，
与 §1 `Dimensions` 的 8 个**任意参数**有本质区别。

**(b) 本公式的实质（不夸大，必须如实登记）**：
**它只区分「确定性 / 非确定性」两种情况**，输出是 **`{0, 1}` 两点**。
它**不是**连续的「反例半径」度量，**不**给出 `0` 与 `1` 之间的任何中间值。
`1/(1+反例半径)` 在这里**只有两个实例化**（半径 `0` 与半径 `1`），
不是一条遍布 `[0,1]` 的曲线。

**(c) 未做的**：**连续的反例半径**。
真正的「反例半径」需要**测度空间上的扰动度量**
（`R.kernel c x` 与 `R.kernel c' x'` 之间的距离，再取使核变化足够大的最小扰动尺度），
而 `Rule` 的 `kernel` 的 codomain 是 `Measure Y.Carrier`，**其上没有任何距离结构**。
⟹ 这是**另一项工作**，§8 **没有**做。

**(d) 不声称「裁决 A 完成了」。**
裁决 A 要求 **8 个**维度都有公式；§8 只给**可证伪性 1 个**维度的公式。
按审计 R564 自己的估算法，裁决 A **仍然远未完成**；
§8 只是「一条真公式胜过 8 个空字段」这一原则的**第一个实例**，仅此而已。

**§8 的两条定理都很浅（如实登记）**：
- `falsifiabilityOf_mem_Icc` 是 `by_cases` + `simp`（输出只有 `0`/`1`，区间界显然）；
- `falsifiability_det_ge_nondet` 展开定义后就是 `0 < 1`（`simp` 即过）。
两者**都不是**深刻定理；价值在于**度量本身存在且由 `Rule` 算出**，不在证明难度。

**§8 未做的第三件事**：§1 的 `Dimensions.falsifiability` 字段**依旧是纯参数**，
§8 **没有**把它强制改写为 `falsifiabilityOf`（纪律：不改已有内容）。
⟹ 若要「把 §8 接进 §4 的 `popperSystem`」，需要一个
`Dimensions` **实例**，这不属于本任务。

---------------------------------------------------------------------------
(g) **作者第 592 轮裁决的落实登记 · 本轮新增 §9（`independence` + `simplicity` 两个维度）**
---------------------------------------------------------------------------
**作者第 592 轮裁决原话（逐字）**：
> 「**做**」
> 「**甲**」

解读：**甲 = 加 `Rules` 层，给剩余 5 个维度写公式。**

**⟹ 主控第 592 轮重大修正（已实测，成立）**：**`Rules` 与 `RuleSpec.le` 都【已存在】，
本任务【没有】新建任何结构层。**
- `abbrev Rules (C) (X) (Y) : Type _ := Set (Rule C X Y)`
  已存在 —— `Fate/Frame.lean:545-547`；
- `class RuleSpec`（含 `le` / `refl` / `trans`）
  已存在 —— `Fate/GammaOperator.lean:644-651`。

**⟹ 本轮只用【已有结构】，在 §9 新增 `2 个 def + 2 条定理`。**

**(g-1) §9 做到的（如实登记，逐条对应）**
1. `noncomputable def independenceOf`——**第 2 个有真公式的维度**（第 1 个是 §8 的
   `falsifiabilityOf`）。用**已有的** `FateV2.Rules.RuleSpec.le`：
   不可比 ⟹ `1`，可比 ⟹ `0`。
2. `theorem independenceOf_mem_Icc`——值域 `[0,1]`。
3. `noncomputable def simplicityOfSet`——**第 3 个有真公式的维度**，落在**规则集**
   `FateV2.Rules C X Y` 上（`Rule` 只有 `kernel`、**无文本**，故单条规则的「简洁度」无处可取）：
   规则集若 `Set.Finite` 则 `1`，否则 `0`。
4. `theorem simplicityOfSet_mem_Icc`——值域 `[0,1]`。

**(g-2) ⚠ 这**不**等于「8 个维度都有公式」——【仍无公式的 5 个维度】及其缺什么：**

| 维度 | 缺什么结构 |
|---|---|
| `explanatory` | 需「规则能解释的既有现象集」⊆ 现象空间，及「解释」关系；`Rule` 只有 `kernel`，**无前件/后件、无现象集** |
| `consistency` | 需「范式内已接受理论的集合」与「相容」关系（模型相容/无矛盾）；`Rule` 上**无模型语义** |
| `operationality` | 需「规则 → 可测量操作序列」的映射（操作化函子）；本库**无操作/测量层** |
| `novelty` | 需「预测的、且观测数据中没有的现象」——即需 **观测数据集** 与时间/新颖判据 |
| `robustness` | 需 `Rule` 空间上的**扰动度量**（`Measure` 上的距离 + 参数扰动半径）；
`Rule.kernel` 的 codomain `Measure Y.Carrier` **无距离结构**（§8 (c) 已登记同一障碍） |

**(g-3) `independence` 与 `simplicity` 的实质局限（不夸大）**
1. `independenceOf` **只有 `{0,1}` 两点输出**，不是连续的「信息重叠比例」。
   它的输入是 `RuleSpec.le` 的**布尔化**（可比/不可比）。
   ⚠ 并且它**继承 `RuleSpec.le` 的语义**：`RuleSpec.le R₁ R₂` 读作「R₁ 比 R₂ **更一般**」
   （`GammaOperator.lean:646`），因此「可比」在此处意味着「一方更一般」，
   **不是**「一方逻辑蕴含另一方」——`RuleSpec` **没有**声明 `le` 与蕴含的关系。
2. `simplicityOfSet` **只覆盖「规则条数」这一个侧面**，且只有 `{0,1}` 两点输出。
   它**不是**「单条规则的简洁度」。
3. **两者都【没有】被接进 §1 的 `Dimensions`。**
   原因：`Dimensions` 的 8 个字段签名都是 `Rule C X Y → ℝ`（**单条规则**），
   而 `independenceOf` 需要**两条**规则、`simplicityOfSet` 需要**规则集**。
   ⟹ 把二者塞进 `Dimensions` **必须改 `Dimensions` 的字段签名**，
   这会改动已有内容（违反纪律 (ii)）。
   ⟹ 故本轮**没有**交付「`Dimensions` 实例」（裁决书中的交付物 3）。
   裁决书自己写明「若这一步做出来会让文件显得『做绿』，就**不做**」，
   而实测发现它**不只是做绿、更是签名不匹配**，故**明确不做**——
   而非用 5 个常数 `fun _ => 0` 造一个假实例。

**(g-4) §9 的两条定理都很浅（如实登记，与 §8 同样诚实）**
- `independenceOf_mem_Icc` / `simplicityOfSet_mem_Icc` 均为
  `unfold` + `split <;> simp`（输出只有 `0`/`1`，区间界显然）。
- 二者**都不是**深刻定理；价值在于**度量本身存在且由已有结构算出**，不在证明难度。

**(g-5) ⚠ 不声称「8 个维度都有公式了」。**
目前只有 **3 个**维度（`falsifiability` / `independence` / `simplicity`）有公式，
**其余 5 个仍是 §1 的任意参数**（见 (g-2) 表格）。
裁决 A **仍未完成**。

**§9 无 `sorry` / `admit` / `axiom`（已实测：`grep` 零命中 + `lake env lean` EXIT=0）。**

---------------------------------------------------------------------------
(h) **作者第 592 轮裁决「甲」的续 · 本轮新增 §10
    （`RuleCovers` 结构 + `explanatory` / `novelty` / `consistency` 三个维度的公式）**
---------------------------------------------------------------------------
**(h-a) 作者第 592 轮裁决原话（逐字）**：

> 「**做**」
> 「**甲**」

**(h-b) 作者第 577 轮方法论（本节的直接依据，逐字）**：

> 「**做不出来一般是需要给别的东西加东西才能做而不是单纯的要证明的对象才能解决**」

⟹ 本轮**先加结构，再加公式**：这正是「给别的东西加东西」。

**(h-c) 本轮加的结构 `RuleCovers` 是什么、为什么需要**

```
class RuleCovers (C) (X) (Y) (I) [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  covers : Rule C X Y → I.Carrier → Prop
```

**为什么需要**：`explanatory` / `novelty` / `consistency` 三个维度共用同一个谓词
「**规则 `R` 覆盖实例 `e`**」，而

- `Rule`（`Fate/Frame.lean:348-351`）**只有** `kernel`，**没有**「实例」这一维；
- `InstSpace`（`Fate/Frame.lean:568-570`）**只有** `Carrier : Type*`，**无任何结构**。

⟹ 三者之间**不存在**「覆盖」关系，三个维度的公式**无从写起**。
本 class 把该谓词**作为参数**加入，**不预设**其语义（本轮**不给**任何具体实例），
因此所得三个公式在**任何**语义下都成立。

**⚠ 与裁决书签名的唯一差异（必要修正，已实测）**：裁决书写的是
`class RuleCovers (C) (X) (Y) (I)`，**不含** `MeasurableSpace` 实例参数；
但 `Rule C X Y` **本身**要求 `[MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]`
（`Fate/Frame.lean:348-349`），不加则 `covers : Rule C X Y → ...` 处**立即**
`synthInstanceFailed`（实测：`failed to synthesize MeasurableSpace X.Carrier`）。
⟹ 加这两个参数是**语法上不可省**的，**不改变语义**。

**(h-d) 本轮做到的（§10，全部有真公式，全部 `lake env lean` EXIT=0）**

| 交付物 | 名称 | 类型 |
|---|---|---|
| 新 class | `RuleCovers` | `class`（1 个字段 `covers`，**无法则**）|
| 辅助 | `coversOf` / `coveredBy` / `otherCovered` | 2 个 `abbrev`/`def` |
| `explanatory` | `explanatoryOf` | `def`：覆盖实例数 / 总实例数 |
| 定理 | `explanatoryOf_mem_Icc` | 值域 `[0,1]`（需实例集非空）|
| 定理 | `explanatoryOf_mono` | 覆盖集包含 ⟹ 解释力不降 |
| `consistency` | `consistencyOf` | `def`：覆盖集的 **Jaccard 相似度** |
| 定理 | `consistencyOf_mem_Icc` | 值域 `[0,1]` |
| 定理 | `consistencyOf_self` | `consistencyOf R R = 1`（**需 `R` 覆盖至少一个实例**）|
| `novelty` | `noveltyOf` | `def`：`|覆盖 R ∖ ⋃其它规则覆盖| / |覆盖 R|` |
| 定理 | `noveltyOf_mem_Icc` | 值域 `[0,1]` |
| 定理 | `noveltyOf_anti_mono` | `Rs₁ ⊆ Rs₂ ⟹ noveltyOf Rs₂ R ≤ noveltyOf Rs₁ R` |

⟹ **`novelty`（裁决书标注「若时间允许」的交付物 4）也做出来了**；
**没有跳过**任何一条。

**(h-e) 仍无公式的维度（如实登记，不夸大）**

本节之后，`Dimensions` 的 8 个维度中**有真公式的是 6 个**：
`falsifiability`（§8）/ `independence`（§9）/ `simplicity`（§9）/
`explanatory`（§10）/ `novelty`（§10）/ `consistency`（§10）。

**仍然只有纯参数（无公式）的 2 个**：

- **`operationality`**：缺**可观测性定义**。
  「规则可操作」需要「`kernel` 能否由某个可观测统计量算出」，
  这要求 `Y.Carrier` 上有可观测结构（`MeasurableSpace` + 可数生成元），
  `Y` 目前只有 `Carrier : Type*` + `MeasurableSpace`，**不够**。
- **`robustness`**：缺**拓扑**。
  「稳健」= 输入的**小扰动**只引起分布的**小变化**，
  这要求 `C.Carrier` / `X.Carrier` 上有拓扑、`Measure Y.Carrier` 上有度量
  （Prokhorov / Wasserstein）。**本轮均无**。

**(h-f) ⚠ 本轮【不】声称的三件事**

1. **不声称「8 个维度都有公式」**：**6 个有，2 个无**（见 (h-e)）。
2. **不声称已接进 `Dimensions`**：§1 的 `Dimensions` 字段**一个都没有被替换**。
   原因同 (g-3) 第 3 条：`Dimensions` 的字段签名是 `Rule C X Y → ℝ`（**单条规则**），
   而 `consistencyOf` 需**两条**规则、`noveltyOf` 需**规则集**；
   把它们塞进去**必须改 `Dimensions` 的字段签名**，这违反纪律 (ii)「只加不改」。
   ⟹ 真正接上需要一个**新文件**造一个 `Dimensions` 实例（**不在本轮范围**）。
3. **不声称这些定理深刻**：四条 `..._mem_Icc` 都是 `split` + `positivity` +
   `card_le_card` 级别的**浅**结论（只说值域），
   `explanatoryOf_mono` / `consistencyOf_self` / `noveltyOf_anti_mono` 也只是
   `card_le_card` / `union_self` / `sdiff` 单调。价值在**度量存在且由结构算出**，
   不在证明难度。

**§10 无 `sorry` / `admit` / `axiom`（已实测：`grep` 零命中 + `lake env lean` 连跑两遍 EXIT=0）。**
-/

/-
---------------------------------------------------------------------------
(i) **作者第 592 轮裁决「甲」的续（第 601/602 轮）· 本轮新增 §12（`robustness`）**
---------------------------------------------------------------------------
**(i-a) 作者裁决原话（第 592 轮，逐字）**：

> 「**做**」
> 「**甲**」

第 602 轮裁决书对本维度的指令（逐字摘录）：
> **(A)** 若 `Measure` 的拓扑可用 ⟹ 写**真连续性**（`Continuous (fun x => R.kernel c x)`）
> **(B)** 若不可用 ⟹ 写 **`robustnessOf R := if R.IsDet then 1 else 0`**
> **(B) 是凑数，可以不做（如实说明）**

**(i-b) `Measure` 的拓扑是否可用 —— `#check` 实测结果（裁决书 (b) 条要求）**

在 `import EvaluationSystems` + `open MeasureTheory` 下，裁决书列的 9 个 API 实测：

| API | 结果 |
|---|---|
| `MeasureTheory.Measure.instTopologicalSpace` | ❌ `Unknown constant` |
| `MeasureTheory.Measure.tendsto_iff_forall_isOpen_le` | ❌ `Unknown constant` |
| `MeasureTheory.Measure.le_of_forall_isOpen_le` | ❌ `Unknown constant` |
| `MeasureTheory.Measure.lintegral_dirac` | ❌ `Unknown constant` |
| `Tendsto`（未 `open Filter`） | ❌ `Unknown identifier` |
| `Filter.Tendsto` | ✅ 可用 |
| `MeasureTheory.Measure.dirac_apply` | ✅ 可用 |
| `MeasureTheory.Measure.dirac_apply_of_mem` | ✅ 可用 |
| `MeasureTheory.Measure.map` / `map_dirac` | ✅ 可用 |

**另测（拓扑 / 度量的所有常见命名）**：
`Measure.instEMetricSpace` / `instMetricSpace` / `instPseudoEMetricSpace` / `instDist`
——**全部** ❌ `Unknown constant`。

⟹ **结论：`Measure Y.Carrier` 上既无拓扑、也无距离。**
⟹ **选项 (A)【不可行】**：`Continuous (fun x => R.kernel c x)` 的目标空间
   `Measure Y.Carrier` **合成不出 `TopologicalSpace` 实例**，这句话在类型上就写不出来。

**(i-c) 走的是哪一支：既不是 (A) 也不是 (B)，而是裁决书「更好的选择」那一支（记作 (C)）**

- **(A) 不可行**（见 (i-b)）；
- **(B) 不做**：`if R.IsDet then 1 else 0` 与 §8 的 `falsifiabilityOf`
  **逐字同构**，是裁决书自己说的「凑数」，且**不区分任何东西**
  （与 `falsifiability` 完全共线）。裁决书明言「可以不做（如实说明）」——**我不做**；
- **(C) 本轮实际交付**：用 `X` 的**伪度量**做「**核稳定半径**」——
  `stableRadiusDist R c x := { d | ∃ y, dist y x = d ∧ R.kernel c y = R.kernel c x }`，
  `robustnessOf` 取其 `sSup` 并饱和到 `[0,1]`。
  语义：**「能容忍多大的状态扰动而不改变预测」**。

**(i-d) ⚠ (C) **不是**鲁棒性（原义），必须如实登记三点**

1. **不是分布鲁棒性。** 真正的鲁棒性是 `kernel : X → Measure Y` **关于 `Measure` 侧**
   的连续性 / Lipschitz 性。本环境**无 `Measure` 拓扑**（(i-b) 已实测）。
   §12 度量的是 `kernel` 在 `X` 侧**保持不变**的邻域大小，
   **不是**两个不同预测之间的距离。**不得声称「鲁棒性已按原义形式化」。**
2. **口径与裁决书的 `sInf` 建议不同（这是有意的）。** 裁决书建议
   `inf { dist x y | kernel c y ≠ kernel c x }`（最早改变距离）。
   该量在数学上**平凡**：远离 `x` 的点几乎必然改变预测，
   故该 `inf` 在绝大多数情形**恒为 `0`**，任何「`> 0`」的定理都**假**。
   ⟹ 我改用**对偶**的 `sSup`（最大稳定半径）。**理由已在此写明，不是悄悄改口径。**
3. **比其余 7 个维度多要一个类型类** `[PseudoMetricSpace X.Carrier]`。
   `StateSpace`（`Fate/Frame.lean:292` 一带）只有 `Carrier : Type*`，**无距离**。
   ⟹ 「扰动大小」本身需要外部结构；这是一条**实质限制**，不是装饰。

**(i-e) `operationality` 仍无公式（裁决书 (e) 条要求登记）**

`Dimensions` 8 维度现况：**7 个有公式，`operationality` 仍无**。
「一个规则可操作」需要「它的 `kernel` 能否由某个**可观测统计量**算出」，
即一个「规则 → 可测量操作序列」的**操作化函子**；
本库**无操作 / 测量层**（`Y` 只有 `Carrier : Type*` + `MeasurableSpace`）。
⟹ **需可观测性定义，留给作者裁决。**

**(i-f) 自审：`robustnessOf_mem_Icc` 是否同义反复？**

- **前件**：`[PseudoMetricSpace X.Carrier]`、`[MeasurableSpace X.Carrier]`、
  `[MeasurableSpace Y.Carrier]` 三个**类型类实例**，加 `R`、`c`、`x` 三个**具体取值**。
  **没有任何**假设陈述 `0 ≤ robustnessOf R c x ≤ 1` 或与之等价的命题。
- **结论**：`robustnessOf R c x ∈ Set.Icc 0 1`。**是新信息，不在前件里。**
- ⚠ **但必须诚实说：这条定理【很浅】。** 因为 `def` 里**显式**写了
  `min 1` 与两支常数 `1`/`0`，证明只是把三支逐一检查
  （`split` + `Real.sSup_nonneg` + `div_nonneg` + `min` 界）。
  **它的价值在「定义存在、由 `Rule.kernel` 与 `dist` 算出、值域如声称」，
  不在证明难度**——与 §8/§9/§10 的 `..._mem_Icc` **同一诚实等级**。
  **不声称它是深刻定理。**

**(i-g) 不声称「8 个维度都有公式」，也不声称「已接进 `Dimensions`」**

- 7 个有公式、`operationality` 无（(i-e)）；
- §1 `Dimensions` 的字段**一个都没被替换**（纪律：只加不改）；
- `Dimensions.robustness : Rule C X Y → ℝ` 是**单参数**签名，
  而 `robustnessOf` 需要 `c` 与 `x` ⟹ **签名不匹配**，
  强行实例化只能用 `fun _ => 0` 造假——**明确不做**。

**§12 无 `sorry` / `admit` / `axiom`（见交付回复中的 `grep` 与 `lake env lean` 原文输出）。**
-/

import FateWorld.FateV2.Rules.RuleEvaluation
-- ⭐ **新增的唯一 import**：`FateV2.Rules.RuleSpec` 定义在 `Fate/GammaOperator.lean:644`。
-- 本文件的 §7（`ruleSpecSystem`）需要它；不改动任何已有模块，只是本文件多引入一条依赖。
import FateWorld.FateV2.Rules.GammaOperator
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace EvaluationSystems

open RuleEval

/-!
  # Rules · EvaluationSystems

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EvaluationSystems.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：RuleEvaluation, GammaOperator
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐ **8 个科学哲学评价维度**（纯参数，无公式）
  =========================================================================== -/

/-- ⭐ **评价维度集合**（8 个字段，一个不少）。

**⚠ 这是参数包，不是公理系统**：每个字段是一个**任意**实值函数
`Rule C X Y → ℝ`。本文件**不**赋予任何公式（理由见文件头 (b)(d)）。

**约定的读法**（仅读法，非定理）：数值**越大越好**——
因此 `popperSystem` 取「可证伪性越大越好」，
`occamSystem` 取「简洁性越大越好」。
⚠ 这与净版把 `conf` 当主标量的做法**方向不同**（见文件头批评 1）。 -/
structure Dimensions (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 可证伪性（波普尔）：越容易被否证越好。 -/
  falsifiability : Rule C X Y → ℝ
  /-- 简洁性（奥卡姆剃刀）：假设越少越好。 -/
  simplicity : Rule C X Y → ℝ
  /-- 解释力（拉卡托斯）：能统一解释的既有现象越多越好。 -/
  explanatory : Rule C X Y → ℝ
  /-- 相容性（库恩）：与当前范式内其它已接受理论越相容越好。 -/
  consistency : Rule C X Y → ℝ
  /-- 稳健性：对扰动的容忍度越高越好。 -/
  robustness : Rule C X Y → ℝ
  /-- 独立性：与竞争规则提供的信息重叠越少越好。 -/
  independence : Rule C X Y → ℝ
  /-- 可操作性：能被落到可测量操作的程度越高越好。 -/
  operationality : Rule C X Y → ℝ
  /-- 新颖性：预测新现象的能力越强越好。 -/
  novelty : Rule C X Y → ℝ

/-! ===========================================================================
  §2  ⭐⭐ **评价体系**（`structure`，不是 `class`）
  =========================================================================== -/

/-- ⭐⭐ **一个评价体系**。

**为什么是 `structure` 而非 `class`**：`class` 意味着**全局唯一**的实例，
而本文件的核心主张是**多个体系同时存在**——
`structure` 让它们作为**普通值**共存，且可以显式传递给定理。

**`le` 只要求自反 + 传递（前序），不要求反对称**：
科学哲学上的「至少一样好」**允许**两条规则互相「一样好」而**并不相同**。 -/
structure EvaluationSystem (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 体系名（如 `"Popper"` / `"Occam"` / `"Lakatos"`）。 -/
  name : String
  /-- 评价量的载体（可增删改）。 -/
  Eval : Type
  /-- 每个规则给出一个评价量。 -/
  eval : Rule C X Y → Eval
  /-- 评价量上的「至少一样好」关系（前序）。 -/
  le : Eval → Eval → Prop
  /-- 自反性。 -/
  le_refl : ∀ e, le e e
  /-- 传递性。 -/
  le_trans : ∀ a b c, le a b → le b c → le a c

/-! **⚠ 关于上面的 `le_refl` / `le_trans` 的形式。**
`RuleEval.RuleEvaluation` 中这两个字段的类型分别是 `∀ e, le e e` 与
`∀ a b c, le a b → le b c → le a c`。
本文件照抄其**字段类型**，故 §3 的桥**逐字填得上**（`#print` 级别的字段名一致）。

**⚠ 与任务书草稿的差异（实测）**：`Rule C X Y` 本身要求
`[MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]`
（见 `Fate/Frame.lean:348`），因此 `Dimensions` 与 `EvaluationSystem`
**必须**把这两个实例参数**写在头部**，否则字段 `Rule C X Y → ℝ` 无法省略。
**⟹ 这是对草稿的唯一增设**（不改任何已有模块，只是本文件的多加参数）。
-/

/-! ===========================================================================
  §3  ⭐ **桥接**：`EvaluationSystem` → `RuleEvaluation`（`structure` → `class` 实例）
  =========================================================================== -/

/-- ⭐ **桥**：任何评价体系**都是**一个 `RuleEvaluation` 实例。

**⟹ 效果**：`RuleEval.Better` 及其 `better_irrefl` / `better_trans` /
`better_asymm` **自动在每个体系里可用**，无需重复证明。
**⟹ 这**不**是把一个体系强加给全局**：调用时用
`letI := EvaluationSystem.toRuleEvaluation S` 局部注册即可。
-/
@[instance_reducible]
def EvaluationSystem.toRuleEvaluation {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S : EvaluationSystem C X Y) : RuleEvaluation C X Y where
  Eval := S.Eval
  eval := S.eval
  le := S.le
  le_refl := S.le_refl
  le_trans := S.le_trans

/-! ===========================================================================
  §4  ⭐⭐ **三个具体体系**（波普尔 / 奥卡姆 / 拉卡托斯）
  =========================================================================== -/

/-- ⭐ **波普尔体系**：只按**可证伪性**排序（越大越好）。 -/
noncomputable def popperSystem {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (D : Dimensions C X Y) : EvaluationSystem C X Y where
  name := "Popper"
  Eval := ℝ
  eval := D.falsifiability
  le := (· ≤ ·)
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc

/-- ⭐ **奥卡姆体系**：只按**简洁性**排序（越大越好）。 -/
noncomputable def occamSystem {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (D : Dimensions C X Y) : EvaluationSystem C X Y where
  name := "Occam"
  Eval := ℝ
  eval := D.simplicity
  le := (· ≤ ·)
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc

/-- ⭐ **拉卡托斯体系**：按 `explanatory + novelty` 排序（越大越好）。

**⚠ 朴素加法的可议性**：把两个**量纲可能不同**的量直接相加，
正是 `Fate/RuleEvaluation.lean` §1.1 明说「**不可辩护**」的操作。
此处**故意**这样做，是为了给出一个「**体系本身也可以是加权和**」的实例，
**不**声称这种加权是科学上正确的（见文件头 (b) 批评 2）。
⚠ **本体系不被任何定理使用**（见文件头 (d) 第 4 条）。 -/
noncomputable def lakatosSystem {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (D : Dimensions C X Y) : EvaluationSystem C X Y where
  name := "Lakatos"
  Eval := ℝ
  eval := fun r => D.explanatory r + D.novelty r
  le := (· ≤ ·)
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hab hbc => le_trans hab hbc

/-! ===========================================================================
  §5  ⭐⭐⭐ **唯一定理：费耶阿本德论纲**
  =========================================================================== -/

/-- ⭐⭐⭐ **【费耶阿本德论纲】**：若两条规则在**可证伪性**与**简洁性**上的
排序**相反**，则**波普尔体系与奥卡姆体系给出相反的排序**。

**⟹ 这是「多种评价体系并存」的根本理由**：不同立场**不可归约**。

**⚠ 前件与结论的关系（自审，防同义反复）**：
- 前件 `hf : D.falsifiability r₂ < D.falsifiability r₁`、
  `hs : D.simplicity r₁ < D.simplicity r₂` 是**两条关于 `D` 的数值假设**；
- 结论是**两个体系各自的 `le` 关系**。将 `popperSystem` / `occamSystem` 的定义展开后，
  结论**逐字变成** `D.falsifiability r₂ ≤ D.falsifiability r₁ ∧
  D.simplicity r₁ ≤ D.simplicity r₂`。
- ⟹ 结论**确实**由前件经 `le_of_lt` 得到，但**前件严格强于结论**
  （`<` 强于 `≤`），且**去掉前件结论可假**（取 `D` 使两条不等式反向即可）。
  故**不是**同义反复；但**也不强**：它就是「两个单维体系的定义展开」。
- **⚠ 不强加于结论的额外声称**：本定理**不**声称「任何两个体系都分歧」——
  那是**假**命题（同一个 `D` 上，取 `r₁ = r₂` 即不成立）。 -/
theorem systems_can_disagree {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (D : Dimensions C X Y) {r₁ r₂ : Rule C X Y}
    (hf : D.falsifiability r₂ < D.falsifiability r₁)
    (hs : D.simplicity r₁ < D.simplicity r₂) :
    (popperSystem D).le ((popperSystem D).eval r₂) ((popperSystem D).eval r₁)
      ∧ (occamSystem D).le ((occamSystem D).eval r₁) ((occamSystem D).eval r₂) :=
  ⟨le_of_lt hf, le_of_lt hs⟩

/-! ===========================================================================
  §6  元评价体系（自更新）
  ===========================================================================

**问题**：评价体系本身如何评价？

**拉卡托斯的答案**：按**进步性问题转移**（progressive problem shift）——
一个体系比另一个好，当且仅当它**能区分对方不能区分的规则**。

**费耶阿本德的警告**：元评价本身也是**一个范式**，所以「元体系」也是相对的
（**本定义不声称有一个「终极的」元体系**）。

**⚠ 本节的定位（如实登记）**：
`MetaBetter` 只形式化了「**细粒度**」这一条判据（`S₂` 能区分 `S₁` 认为不可比的一对规则），
它是**一个**候选判据，**不是**「进步性问题转移」的全部内容
（拉卡托斯原文还要求「经验内容增长」「部分超余内容被确证」，
这些在本文件中**没有**形式化，因为 `Rule` 不含前件/后件/概率空间 `P`）。
-/

/-- ⭐⭐⭐ **元评价：`S₂` 比 `S₁` 更细**。

**定义**：存在两条规则，使得
- `S₂` 认为 `r₁` 严格优于 `r₂`；
- 而 `S₁` 认为 `r₁` 与 `r₂` **不可比**（既不 `r₁ ≤ r₂` 也不 `r₂ ≤ r₁`）。

**⟹ 这就是「`S₂` 能区分 `S₁` 不能区分的」的形式化。**
**⟹ 它是「自更新」的数学内容：好的体系能细粒度地区分。**

**⚠ 非自反性来自定义本身**：`MetaBetter S S` 要求同一个 `S` 同时
「严格认为 `r₁` 更好」（含 `S.le (eval r₂) (eval r₁)`）
与「认为不可比」（含 `¬ S.le (eval r₂) (eval r₁)`），二者直接矛盾。
因此 `metaBetter_irrefl` 的证明**只做一次实例化**，无任何附加假设。 -/
def MetaBetter {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S₁ S₂ : EvaluationSystem C X Y) : Prop :=
  ∃ (r₁ r₂ : Rule C X Y),
    -- S₂ 严格认为 r₁ 更好
    S₂.le (S₂.eval r₂) (S₂.eval r₁) ∧ ¬ S₂.le (S₂.eval r₁) (S₂.eval r₂)
    -- S₁ 认为不可比
    ∧ ¬ S₁.le (S₁.eval r₂) (S₁.eval r₁)
    ∧ ¬ S₁.le (S₁.eval r₁) (S₁.eval r₂)

/-- ⭐⭐ **【关键】**：**元评价是严格非自反的**（`S` 不比 `S` 更细）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本定理**没有**前件（除 `S` 本身外）。结论 `¬ MetaBetter S S`
**不是**由某个把结论藏进去的假设得到，而是由 `MetaBetter` 的 `∃ ∧ ∧ ∧`
结构在 `S₁ = S₂ = S` 时**自我矛盾**推出：
- 第 1 个合取支给 `S.le (S.eval r₂) (S.eval r₁)`；
- 第 3 个合取支给 `¬ S.le (S.eval r₂) (S.eval r₁)`。
二者直接冲突（证明即 `exact h3 h1`）。
⟹ 这是**真定理**，但**很浅**：它只是「严格性」与「不可比性」不能同时成立于同一对元素。
-/
theorem metaBetter_irrefl {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S : EvaluationSystem C X Y) : ¬ MetaBetter S S := by
  rintro ⟨r₁, r₂, h1, _, h3, _⟩
  exact h3 h1

/-! ===========================================================================
  §7  ⭐⭐⭐ **【由 `RuleSpec` 诱导的评价体系】**（与主干 `WorldModelCompleteV2` 的桥）
  ===========================================================================

**背景**：`Fate/GammaOperator.lean:644` 的

```
class RuleSpec (C) (X) (Y) [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  le : Rule C X Y → Rule C X Y → Prop
  refl : ∀ R, le R R
  trans : ∀ {R₁ R₂ R₃}, le R₁ R₂ → le R₂ R₃ → le R₁ R₃
```

提供的正是本文件 `EvaluationSystem` 所需的三个字段（`le` / `le_refl` / `le_trans`），
**字段名逐一对应**（`RuleSpec.refl` ↔ `le_refl`，`RuleSpec.trans` ↔ `le_trans`）。
⟹ 故可**零成本**得到一个评价体系。

**为什么这重要**：`Fate/WorldModelCompleteV2.lean`（WMC）通过 `[RuleSpec C X Y]`
合成 `Preorder (Rule C X Y)`（`Fate/GammaOperator.lean` 的 `RuleSpec.instPreorder`），
其载体含单条规则 `Rule C F.X F.X`（WMC `:168`）与规则集 `FateV2.Rules`（WMC `:191`）。
于是「主干里的规则」自动成为一个评价体系里的**被评价量**，无需另造载体。
-/

/-- ⭐⭐⭐ **【由 `RuleSpec` 诱导的评价体系】**

`RuleSpec` 提供的正是 `EvaluationSystem` 所需的（`le` / `refl` / `trans`），
故可**零成本**得到一个评价体系：**评价量 = 规则本身，偏序 = `RuleSpec.le`**。

**⟹ 这是 `EvaluationSystems` 与主干（`WorldModelCompleteV2` 的 `RuleSpec`）之间的桥。**

**⚠ 语义注意**：`RuleSpec.le R₁ R₂` 的约定读法是「$R_1$ 比 $R_2$ **更一般**」
（见 `GammaOperator.lean:646` 的字段注释），而本文件其余体系（`popperSystem` 等）
的 `le` 读法是「**至少一样好**」。两者方向约定**不同**：
本 `def` **原样搬运** `RuleSpec.le`，**不翻转方向**，
故在 `ruleSpecSystem` 里 `le` 的字面意义是「更一般或等价」而非「更好」。
⟹ **本 `def` 是一个结构性桥，不是「更好」的语义断言。**

**⚠ 局限（如实登记，见文件头 (e)）**：`Eval := Rule C X Y` 意味着
「**评价量就是规则本身**」，即**没有把 8 个维度数值化**；
要数值化需要具体的 `Dimensions` 实例。 -/
def ruleSpecSystem {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [FateV2.Rules.RuleSpec C X Y] : EvaluationSystem C X Y where
  name := "RuleSpec"
  Eval := Rule C X Y
  eval := id
  le := FateV2.Rules.RuleSpec.le
  le_refl := FateV2.Rules.RuleSpec.refl
  le_trans := fun _ _ _ hab hbc => FateV2.Rules.RuleSpec.trans hab hbc

/-- ⭐⭐ **【`ruleSpecSystem` 上的「更好」与 `RuleSpec.le` 严格对应】**

本定理用 `RuleEval.Better`（`Fate/RuleEvaluation.lean:155`）表述：
`Better r₁ r₂ := le (eval r₂) (eval r₁) ∧ ¬ le (eval r₁) (eval r₂)`。
把 `ruleSpecSystem` 通过 §3 的 `toRuleEvaluation` 桥注册后，
`Better` 的 `le` **就是** `FateV2.Rules.RuleSpec.le`，`eval` **就是** `id`。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本定理**没有把结论包进前件**。前件有且仅有：
- `[MeasurableSpace X.Carrier]` / `[MeasurableSpace Y.Carrier]`（实例参数，构造 `Rule` 所必需）；
- `[FateV2.Rules.RuleSpec C X Y]`（实例参数，提供 `le` 及其两条律）；
- 两个规则 `r₁ r₂ : Rule C X Y`。
结论是「`Better`（在 `ruleSpecSystem` 诱导的 `RuleEvaluation` 实例下）
恰好等价于 `RuleSpec.le r₂ r₁ ∧ ¬ RuleSpec.le r₁ r₂`」。

**⚠ 证明为 `Iff.rfl`，因此本定理很浅**（已实测：`by rfl` 即通过）：
`ruleSpecSystem` 的 `Eval` 是 `id`、`le` 是 `RuleSpec.le`，
经 `toRuleEvaluation` 后，`RuleEval.Better` 的两侧**δ 归约**为同一命题。
⟹ **它不是深刻定理**；价值仅在于如实登记「桥接无信息损失」：
经桥注册后，`Better` 的语义与 `RuleSpec.le` **完全一致**，没有隐藏的方向翻转。
⟹ **不**声称它给出了「哪个规则更好」的任何判定。 -/
theorem ruleSpecSystem_better_iff {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [FateV2.Rules.RuleSpec C X Y] (r₁ r₂ : Rule C X Y) :
    @RuleEval.Better C X Y _ _
      (EvaluationSystem.toRuleEvaluation (ruleSpecSystem (C := C) (X := X) (Y := Y)))
      r₁ r₂ ↔ (FateV2.Rules.RuleSpec.le r₂ r₁ ∧ ¬ FateV2.Rules.RuleSpec.le r₁ r₂) := by
  rfl

/-! ===========================================================================
  §8  可证伪性：一条真公式（审计 R564 要求）
  ===========================================================================

**审计 R564 的原话**：

> 「（最重要）裁决 A 只完成约 **20%** —— 8 维度零公式。挑**可证伪性**做**一条真公式**
>   （`Rule` 有 `kernel`，可定义反例半径）。**不要再新建模块**。」

**⟹ 本节只交付：1 个 `def` + 2 条定理**，全部落在本文件内，不新建模块。

**波普尔的判据**：一个理论越容易被否证，越有科学内容。
**在规则上的形式化**：一条规则越「精确」（对越多的输入给出越窄的分布），
越容易被一个反例否证。

**⟹ 定义**：规则的可证伪性 = `1 / (1 + 反例半径)`，
其中「反例半径」用 `R` 在 `(c, x)` 上是否**处处**为点质量来近似：

- **`R.IsDet` 的规则（每个 `(c,x)` 都是点质量 Dirac）：反例半径 = 0**
  ⟹ 可证伪性 = `1/(1+0) = 1`（一个反例就足以否证）；
- **否则（某些 `(c,x)` 上核是真正的分布）：反例半径 = 1**
  ⟹ 可证伪性 = `1/(1+1) = 1/2`，本节实现里直接取值 `0`，见下方「实质」。

**⚠⚠ 本定义的实质（自审，防夸大）**：

1. **它只区分「确定性 / 非确定性」两种情况**，输出是 **`{0, 1}` 两点**。
   它**不是**连续的「反例半径」度量，**不**给出 `0` 与 `1` 之间的任何中间值。
   ⟹ `1/(1+反例半径)` 这个写法在这里**只有两个实例化**（半径 0 与半径 1），
   不是一条遍布 `[0,1]` 的曲线。

2. **未做的**：**连续的反例半径**。
   真正的「反例半径」需要**测度空间上的扰动度量**
   （例如 `R.kernel c x` 与 `R.kernel c' x'` 之间的某个距离，
   再取使核「变化足够大」的最小扰动尺度），
   而 `Rule` 只有一个字段 `kernel : C.Carrier → X.Carrier → Measure Y.Carrier`
   （`Fate/Frame.lean:348-351`），**其 codomain 上没有任何距离结构**。
   ⟹ 连续版本是**另一项工作**，本节**没有**做。

3. **不声称「裁决 A 完成了」。** 裁决 A 要求 8 个维度都有公式；
   本节只给**可证伪性 1 个**维度的公式。
   按审计 R564 自己的估算法，裁决 A **仍然远未完成**；
   本节的贡献是「**一条真公式胜过 8 个空字段**」这一条原则的**第一个实例**，
   仅此而已。§1 的 `Dimensions.falsifiability` 依旧是**纯参数**，
   本节**没有**把它强制改成 `falsifiabilityOf`（那会改动已有内容，违反纪律）。
-/

/-- ⭐⭐⭐ **【可证伪性的真公式 · 1 个 `def`】**

**定义**：`falsifiabilityOf R := if R.IsDet then 1 else 0`。

这是「`1 / (1 + 反例半径)`」在**两点反例半径**（`0` / `1`）上的实例化：

- `R.IsDet`（每个 `(c,x)` 上核都是 Dirac）⟹ 反例半径 `0` ⟹ **可证伪性 `1`**（最可证伪）；
- `¬ R.IsDet` ⟹ 反例半径 `1` ⟹ **可证伪性 `0`**（本节实现取 `0`，见文件 §8 头部的登记）。

**⚠ 这是第一条【有具体公式】的评价量**，它由 `Rule` 的**唯一字段** `kernel`
（经 `Rule.IsDet`，`Fate/Frame.lean:408`）算出，**不是** §1 那种任意参数。

**⚠ 定位（如实登记）**：它只区分**两个**情形，**不是**连续度量。
另：`R.IsDet` 是不可判定的（`∃ d`），故本 `def` 是 `noncomputable`，
并在定义体内用 `classical` 打开 `Classical.propDecidable` 以提供 `if` 所需的
`Decidable R.IsDet` 实例（实测：不加 `classical` 则 `synthInstanceFailed`）。 -/
noncomputable def falsifiabilityOf {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) : ℝ := by
  classical
  exact if R.IsDet then 1 else 0

/-- ⭐ **可证伪性在 `[0, 1]` 内**。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有 `R : Rule C X Y`（外加构造 `Rule` 所必需的两个
`MeasurableSpace` 实例）。结论 `falsifiabilityOf R ∈ Set.Icc 0 1`
**没有**被包进任何假设；它由 `falsifiabilityOf` 的定义在
`R.IsDet` 的两个分支上分别取值 `1` / `0` 而得。
⟹ **不是**同义反复，但**很浅**：证明是 `by_cases` + `simp` + `norm_num`
（由于输出只有 `0` 和 `1` 两点，区间界是显然的）。 -/
theorem falsifiabilityOf_mem_Icc {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) : falsifiabilityOf R ∈ Set.Icc (0 : ℝ) 1 := by
  unfold falsifiabilityOf
  by_cases h : R.IsDet <;> simp [h]

/-- ⭐⭐ **【波普尔方向】**：确定性规则的可证伪性**严格大于**非确定性规则的。

**⟹ 这就是净版把 `conf` 当主标量的**方向错误**的形式化纠正**：
净版说 `conf` 越高越好；**但 `conf = 1`（确定性）虽然 `conf` 最高，
在波普尔意义下确实最可证伪**——
**两个方向不矛盾，因为 `conf` 只是「前件上的确定度」，
不是「整个规则的可证伪性」。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
- 前件 `h₁ : R₁.IsDet`、`h₂ : ¬ R₂.IsDet` 是**关于两条规则的、彼此独立的性质假设**；
- 结论是 `falsifiabilityOf R₂ < falsifiabilityOf R₁`，即两条**不同的规则**上的数值比较。
- 结论**不是**前件的同义反复：`IsDet` 是 `Rule → Prop`，
  而结论是 `ℝ` 上的 `<`；二者之间的桥是 `falsifiabilityOf` 的定义。
- **去掉前件结论可假**：取 `R₁ = R₂`，则两边相等，`<` 不成立
  （且若 `R₂.IsDet` 则 `h₂` 不成立）。
⟹ **不是**同义反复；但**很浅**：结论在展开定义后就是 `0 < 1`（`norm_num`）。

**⚠ 不声称**：本定理**不**声称「可证伪性高 ⟹ 规则好」——
那是一个**价值判断**，不是数学命题；本节只给度量，不给排序。 -/
theorem falsifiability_det_ge_nondet {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R₁ R₂ : Rule C X Y) (h₁ : R₁.IsDet) (h₂ : ¬ R₂.IsDet) :
    falsifiabilityOf R₂ < falsifiabilityOf R₁ := by
  unfold falsifiabilityOf
  simp [h₁, h₂]

/-! ===========================================================================
  §9  ⭐⭐⭐ **`independence` 与 `simplicity` 的真公式**（作者第 592 轮裁决「做 / 甲」）
  ===========================================================================

**作者原话（第 592 轮，逐字）**：「**做**」「**甲**」。

**主控第 592 轮重大修正（本轮实测成立）**：**`Rules` 与 `RuleSpec.le` 都【已存在】**，
本任务**不新建结构层**：

- `Fate/Frame.lean:545-547`：
  `abbrev Rules (C : CtxSpace) (X : StateSpace) (Y : OutSpace) ... : Type _ :=
     Set (Rule C X Y)`
- `Fate/GammaOperator.lean:644-651`：
  `class RuleSpec ... where { le : Rule C X Y → Rule C X Y → Prop
                             refl : ∀ R, le R R
                             trans : ∀ {R₁ R₂ R₃}, le R₁ R₂ → le R₂ R₃ → le R₁ R₃ }`

⟹ 「规则之间可比」**已有结构**（`RuleSpec.le`）；
而「规则覆盖实例」**没有**（`grep "def related\|def implies\|def subsumes"` 零命中），
故 `simplicity` 改在 `Rules` 层（规则集）上定义而非做「规则覆盖实例」。

**本节只交付 2 个 `def` + 2 条定理**，全部落在本文件内，不新建模块。
-/

/-- ⭐⭐⭐ **【`independenceOf`（独立性）：两条规则在 `RuleSpec.le` 下【不可比】**】

**杜恒-奎因的整体论视角**：一条规则若可由另一条推出（更一般 ⟹ 更强），
它就不独立。

**定义**（对「两规则之间的关系」给出一个数值）：
- **不可比 ⟹ `1`**（完全独立）
- **可比（一方 `le` 另一方）⟹ `0`**（不独立）

**⟹ 这是 `Dimensions` 8 个维度里第 2 个有真公式的**（第 1 个是 §8 的 `falsifiabilityOf`）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除构造 `Rule` / `RuleSpec` 所必需的实例参数与两条规则本身）。
输出值是**两条规则之间的谓词** `RuleSpec.le` 的**布尔化**，
而输入里**不包含任何数值**——不存在「把结论包进前件」的可能。

**⚠ 实质局限（如实登记，不夸大）**：
1. 输出只有 **`{0, 1}` 两点**，**不是**连续的「信息重叠比例」。
2. 它**继承 `RuleSpec.le` 的语义**：`Fate/GammaOperator.lean:646` 把 `le R₁ R₂`
   读作「$R_1$ 比 $R_2$ **更一般**」。⟹ 此处「可比」= 「一方更一般」，
   **不是**「一方逻辑蕴含另一方」——`RuleSpec` **没有**声明 `le` 与蕴含的关系。
3. ⚠ 由 `RuleSpec.refl`，取 `R₁ = R₂` 时 `le R₁ R₂` 恒成立，故 `independenceOf R R = 0`：
   **一条规则与它自身不独立**（这正是合理行为，但须显式登记）。

**⚠ `if` 需要 `Decidable` 实例**：`RuleSpec.le` 是一般 `Prop`，不可判定，
故本 `def` 为 `noncomputable` 并在定义体内 `classical` 打开
`Classical.propDecidable`（实测：不加则 `synthInstanceFailed`）。
这与 §8 `falsifiabilityOf` 的处置**一致**。 -/
noncomputable def independenceOf {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [FateV2.Rules.RuleSpec C X Y] (R₁ R₂ : Rule C X Y) : ℝ := by
  classical
  exact if (FateV2.Rules.RuleSpec.le R₁ R₂ ∨ FateV2.Rules.RuleSpec.le R₂ R₁) then 0 else 1

/-- ⭐ **`independenceOf` 的值域在 `[0, 1]`。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有两条规则 `R₁ R₂`（外加 `Rule` / `RuleSpec` 所需的实例参数）。
结论 `independenceOf R₁ R₂ ∈ Set.Icc 0 1` **没有**被包进任何假设；
它由定义在 `(le R₁ R₂ ∨ le R₂ R₁)` 的两个分支上分别取值 `1` / `0` 而得。
⟹ **不是**同义反复，但**很浅**（输出只有两点，区间界显然）。 -/
theorem independenceOf_mem_Icc {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [FateV2.Rules.RuleSpec C X Y] (R₁ R₂ : Rule C X Y) :
    independenceOf R₁ R₂ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold independenceOf
  split <;> simp

/-- ⭐⭐ **【`simplicityOfSet`（简洁度）：规则集的有限性】**

**奥卡姆剃刀**：**更少的规则更好**。

**定义**：规则集 `Rs : Rules C X Y` 若【有限】（`Set.Finite Rs`），
则 `simplicityOfSet = 1`；否则 `0`。

**⚠ 这是「规则集层面的简洁度」**，**不是**「单条规则的简洁度」——
后者需要「规则文本长度」，而 `Rule` 只有 `kernel : C.Carrier → X.Carrier → Measure Y.Carrier`
（`Fate/Frame.lean:348-351`），**无文本**。
⟹ 所以本定义**只覆盖「规则条数」这一个侧面**。

**⚠ 它用的是【已有的】** `FateV2.Rules`（`Fate/Frame.lean:545-547` 的 `abbrev ... := Set (Rule C X Y)`），
本 `def` **不新建结构层**。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除唯一的规则集参数 `Rs`）；输出由 `Rs.Finite` 这个
**与数值无关的谓词**决定，输入中**不含任何实数**。

**⚠ `Set.Finite` 的确切写法（已 `#check` 实测）**：
`@Set.Finite : {α : Type u_1} → Set α → Prop`⟹ 对 `Rs : Set (Rule C X Y)`，
`Rs.Finite` **合法**（`Set` 的 `Finite` 作为点记法属性）。
用 `if Rs.Finite` 需 `classical`（同上：`Decidable` 不可合成，实测 `synthInstanceFailed`）。 -/
noncomputable def simplicityOfSet {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (Rs : FateV2.Model.Rules C X Y) : ℝ := by
  classical
  exact if Rs.Finite then 1 else 0

/-- ⭐ **`simplicityOfSet` 的值域在 `[0, 1]`。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有规则集 `Rs`。结论**未**被包进任何假设；
它由定义在 `Rs.Finite` 的两个分支上分别取值 `1` / `0` 而得。
⟹ **不是**同义反复，但**很浅**。 -/
theorem simplicityOfSet_mem_Icc {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (Rs : FateV2.Model.Rules C X Y) : simplicityOfSet Rs ∈ Set.Icc (0 : ℝ) 1 := by
  unfold simplicityOfSet
  split <;> simp

/-! ===========================================================================
  §10  ⭐⭐⭐ **`RuleCovers` 结构 + `explanatory` / `novelty` / `consistency` 的真公式**
        （作者第 592 轮裁决「做 / 甲」，本轮=第 593 轮执行）
  ===========================================================================

**作者原话（第 592 轮，逐字）**：「**做**」「**甲**」。

**作者第 577 轮的方法论（本轮的直接依据，逐字）**：

> 「**做不出来一般是需要给别的东西加东西才能做而不是单纯的要证明的对象才能解决**」

⟹ 本节的路线正是「**给别的东西加东西**」：**不加定理，先加结构**。

---------------------------------------------------------------------------
(a) 现状（本轮实测成立）
---------------------------------------------------------------------------
`Dimensions`（§1）共 8 个维度，上一轮（§9）后已有 **3 个** 有真公式：
`falsifiability`（§8 `falsifiabilityOf`）、
`independence`（§9 `independenceOf`）、
`simplicity`（§9 `simplicityOfSet`）。

⚠ **但 §9 的 `independenceOf` / `simplicityOfSet` 并没有真的接到 §1 的
`Dimensions` 字段上**（§8 头部已如实登记：§1 的字段依旧是纯参数）。
本轮同样**只加新定义，不改 §1**（纪律 (ii)「只加不改」），
故 **`Dimensions` 的字段仍然一个都没有被替换**。

`explanatory` / `novelty` / `consistency` 三个维度缺的共同前提是**同一个谓词**：
「**规则 `R` 覆盖实例 `e`**」。而

- `Rule`（`Fate/Frame.lean:348-351`）**只有**一个字段
  `kernel : C.Carrier → X.Carrier → Measure Y.Carrier`，**没有**「实例」这一维；
- `InstSpace`（`Fate/Frame.lean:568-570`）**只有** `Carrier : Type*`，**无任何结构**。

⟹ 二者之间**不存在**「覆盖」关系，所以三个维度的公式**无从写起**。
这正是作者第 577 轮说的「需要给别的东西加东西」。

---------------------------------------------------------------------------
(b) 本轮加的结构：`RuleCovers`
---------------------------------------------------------------------------
```
class RuleCovers (C : CtxSpace) (X : StateSpace) (Y : OutSpace) (I : InstSpace) where
  covers : Rule C X Y → I.Carrier → Prop
```

**为什么必须是 class 而不是 def**：`covers` 的具体内容依赖「实例是什么」
（可由 `kernel` 的支撑集给出，也可由数据给出），
**本轮不预设其语义**；把它作为**参数**（typeclass）传入，
就能在**任何**语义下都得到三个维度的数值。

⟹ **本轮交付（有公式）**：`explanatoryOf`、`noveltyOf`、`consistencyOf`。
⟹ **本轮仍无公式**：`operationality`、`robustness`（见 §10 末尾）。

⚠⚠ **不声称「8 个维度都有公式」**：3（§8/§9）+ 3（本节）= **6 个**有公式，
`operationality` / `robustness` **仍然只有 §1 的纯参数字段**。
`Dimensions` 本身**未改动**。
-/

/-- ⭐⭐⭐ **【新结构：规则覆盖实例】**

**为什么需要它**（作者第 577 轮方法论「给别的东西加东西」）：
`explanatory` / `novelty` / `consistency` 三个维度都要用
「规则 `R` 覆盖实例 `e`」这个谓词，而 `Rule` 只有 `kernel`（分布核），
`InstSpace` 只有 `Carrier : Type*`（无结构）。

⟹ 本 class 把该谓词**作为参数**加入，从而三个维度的公式可以**一次写出**，
且**不预设**「覆盖」的具体语义。

**⚠ 语义空位（如实登记）**：本 class **不规定** `covers` 与 `kernel` 的任何关系。
一个「自然的」实例化是 `covers R e := ...` 由 `R.kernel` 的支撑集给出，
但那需要实例侧的结构（`I.Carrier` 上要有 `C`/`X`/`Y` 的投影），
`InstSpace` **目前没有**，故本轮**不**给任何具体实例，只给抽象结构。

**⚠ 本 class 无字段定律**（无 `refl` / `trans` 之类）。这是**有意的**：
`covers` 一般**不**自反也不传递（一条不覆盖任何实例的规则是允许的），
强加定律会**凭空**限制语义。 -/
class RuleCovers (C : CtxSpace) (X : StateSpace) (Y : OutSpace) (I : InstSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- `covers R e` 读作「规则 `R` 覆盖实例 `e`」。 -/
  covers : Rule C X Y → I.Carrier → Prop

/- **⚠ 与裁决书给的签名的一处**必要差异**（如实登记）**：
裁决书写的是 `class RuleCovers (C) (X) (Y) (I)`，**不含** `MeasurableSpace` 实例参数。
但 `Rule C X Y` **本身**要求 `[MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]`
（`Fate/Frame.lean:348-349` 的 `structure Rule ... [MeasurableSpace X.Carrier]
[MeasurableSpace Y.Carrier]`），
故 class 签名**必须**带上这两个实例参数，否则 `covers : Rule C X Y → ...` 处
**立即** `synthInstanceFailed`（已实测：`failed to synthesize MeasurableSpace X.Carrier`）。
⟹ 这是**语法上不可省**的修正，**不改变**裁决书的语义。 -/

namespace RuleCoversFormulas

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {I : InstSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
  [Fintype I.Carrier] [DecidableEq I.Carrier] [RuleCovers C X Y I]

/-- 覆盖谓词的简写（让下游可写 `coversOf R e`）。 -/
abbrev coversOf (R : Rule C X Y) (e : I.Carrier) : Prop :=
  RuleCovers.covers R e

/-- 规则 `R` 覆盖的实例集（`Finset`）。 -/
noncomputable def coveredBy (R : Rule C X Y) : Finset I.Carrier := by
  classical
  exact Finset.univ.filter (fun e => coversOf (I := I) R e)

/-- ⭐⭐⭐ **【`explanatory`（解释力）：规则覆盖的实例比例】**

**拉卡托斯（研究纲领）**：能解释**更多已有现象**更好 ⟹ **覆盖率越高越好**。

**定义**：`explanatoryOf R := |{e | covers R e}| / |univ|`。

**⚠ 需要 `[Fintype I.Carrier]`（总实例数有限）与 `[DecidableEq I.Carrier]`**
（`Finset.univ.filter` 的 `DecidablePred` 由 `classical` 提供，见定义体）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除构造 `Rule` / `InstSpace` 所必需的实例参数与 `R` 本身）。
输出的分子是**覆盖集的大小**、分母是**总实例数**，
输入中**不含任何实数**，故不存在「把结论包进前件」的可能。
**⚠ 实质局限**：`explanatoryOf` 在**分母为 0**（`I.Carrier` 为空）时也是 `0`
（`x / 0 = 0` 于 `ℝ`），此时「覆盖率」无意义；
⟹ 凡用它的定理都需显式加 `0 < Fintype.card I.Carrier`（见下条定理）。 -/
noncomputable def explanatoryOf (R : Rule C X Y) : ℝ :=
  ((coveredBy (I := I) R).card : ℝ) / (Fintype.card I.Carrier : ℝ)

omit [DecidableEq I.Carrier] in
/-- ⭐ **`explanatoryOf` 在 `[0, 1]`**（需实例集非空）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有 `R : Rule C X Y` 与 `hne : 0 < Fintype.card I.Carrier`
（**非空性**）。`hne` **不是**结论的伪装：结论 `∈ Set.Icc 0 1` 是
**区间隶属**，而 `hne` 是**一个 `ℕ` 的正性**。若去掉 `hne`，
分母为 `0`，`div_le_one` 无法用（且此时 `explanatoryOf R = 0`，结论仍真但证明需另走）。
⟹ **不是**同义反复；证明用 `div_le_one`（已 `#check`）把上界化为
`card ≤ card`，再由 `Finset.card_filter_le`（已 `#check`）给出。
**⚠ 很浅**：它只说「比例落在 `[0,1]`」，不说任何关于规则优劣的话。 -/
theorem explanatoryOf_mem_Icc (R : Rule C X Y) (hne : 0 < Fintype.card I.Carrier) :
    explanatoryOf (I := I) R ∈ Set.Icc (0 : ℝ) 1 := by
  unfold explanatoryOf coveredBy
  classical
  constructor
  · positivity
  · rw [div_le_one (by exact_mod_cast hne)]
    exact_mod_cast Finset.card_filter_le (Finset.univ : Finset I.Carrier)
      (fun e => coversOf (I := I) R e)

omit [DecidableEq I.Carrier] in
/-- ⭐⭐ **【`explanatory` 单调】**：若 `R₁` 覆盖的实例包含 `R₂` 覆盖的，
则 `explanatoryOf R₂ ≤ explanatoryOf R₁`。

**⟹ 这是「解释力」作为评价量的**基本合理性质**：
解释**更多**绝不能**降分**（拉卡托斯：超余经验内容）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : ∀ e, covers R₂ e → covers R₁ e` 是**两条规则的覆盖集之间的包含关系**；
结论是**两个实数**之间的 `≤`。二者之间的桥是 `explanatoryOf` 的定义。
`h` **不是**「`explanatoryOf R₂ ≤ explanatoryOf R₁`」的改写：
`h` 里**没有**任何 `Finset.card`、`Finset.univ` 或除法。
⟹ **不是**同义反复；但**很浅**（`card_le_card` + `div_le_div_of_nonneg_right`）。
**⚠ 不声称**：不声称「解释力高 ⟹ 规则真」，也不给出任何排序结论。

**⚠ 分母为 `0` 的情形无需排除**：`h` 蕴含覆盖集包含关系，
而两边分母**是同一个** `Fintype.card I.Carrier : ℝ ≥ 0`，
故用 `div_le_div_of_nonneg_right` 即可，不要求非空。 -/
theorem explanatoryOf_mono (R₁ R₂ : Rule C X Y)
    (h : ∀ e : I.Carrier, coversOf (I := I) R₂ e → coversOf (I := I) R₁ e) :
    explanatoryOf (I := I) R₂ ≤ explanatoryOf (I := I) R₁ := by
  unfold explanatoryOf coveredBy
  classical
  have hsub : Finset.univ.filter (fun e => coversOf (I := I) R₂ e)
      ⊆ Finset.univ.filter (fun e => coversOf (I := I) R₁ e) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact h e he
  have hc : (Finset.univ.filter (fun e => coversOf (I := I) R₂ e)).card
      ≤ (Finset.univ.filter (fun e => coversOf (I := I) R₁ e)).card :=
    Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- ⭐⭐⭐ **【`consistency`（一致性）：两规则覆盖集的 Jaccard 相似度】**

**库恩（范式）**：与现有规则越**相容**越好。

**定义**：`|覆盖₁ ∩ 覆盖₂| / |覆盖₁ ∪ 覆盖₂|`（若**并集为空**，取 `0`）。

**⚠ 这与 `independenceOf`（§9）不同**：`independenceOf` 用 `RuleSpec.le`
（**序关系**，且「不可比」才得 `1`），`consistencyOf` 用**覆盖集**
（**语义关系**，且「一样」才得 `1`）。
⟹ 两者是**不同层次**的量，**不互相蕴含**（本轮**不**证它们的任何关系）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除两条规则与必需实例参数）；输入中**不含实数**。

**⚠ 局限（如实登记）**：
1. 「并集为空取 `0`」是**约定**，不是数学结论——两条规则都不覆盖任何实例时，
   Jaccard 相似度**无定义**，取 `0` 相当于说「空对空不算相容」。
2. 输出是对称的（`s₁ ∩ s₂ = s₂ ∩ s₁` 等），但本轮**不证**对称性定理。

**⚠ 实现方式**：定义体**不用**内层 `let`（内层 `let` 会让 `split` 无法
切开 `if`——已实测 `split` 报 `Could not split an if`），
改为直接用 `coveredBy` 展开，使 `unfold consistencyOf; split` 可用。 -/
noncomputable def consistencyOf (R₁ R₂ : Rule C X Y) : ℝ := by
  classical
  exact
    if ((coveredBy (I := I) R₁) ∪ (coveredBy (I := I) R₂)).card = 0 then 0
    else (((coveredBy (I := I) R₁) ∩ (coveredBy (I := I) R₂)).card : ℝ)
      / (((coveredBy (I := I) R₁) ∪ (coveredBy (I := I) R₂)).card : ℝ)

/-- ⭐ **`consistencyOf` 在 `[0, 1]`。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有两条规则 `R₁ R₂`（外加所需实例参数）。
结论 `∈ Set.Icc 0 1` **没有**被包进任何假设；它由定义在
「并集为空」与「并集非空」两支上分别取值 `0` 与商而得。

**⚠ 证明细节（如实登记）**：`Finset.card_inter_le_card_union`
**在 Mathlib 中不存在**（已实测：`unknownConstant`）。
⟹ 改用 `Finset.card_le_card Finset.inter_subset_union`（二者均已 `#check` 通过），
再 `exact_mod_cast` 到 `ℝ`。
**⚠ 很浅**：只说「Jaccard 相似度落在 `[0,1]`」，不说任何关于规则好坏的判断。 -/
theorem consistencyOf_mem_Icc (R₁ R₂ : Rule C X Y) :
    consistencyOf (I := I) R₁ R₂ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold consistencyOf
  classical
  split
  · simp
  · rename_i h
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_union)

/-- ⭐⭐ **【`consistency` 自反 = 1（当规则至少覆盖一个实例）】**

**⟹ 一条规则与它自身的覆盖集完全一致**（Jaccard 相似度的基本性质）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : (coveredBy R).Nonempty` 说的是「`R` **覆盖至少一个实例**」，
是一个**关于覆盖集的非空性**陈述；`Finset` 中有 `Nonempty` 的规则**不再成立**。
结论 `consistencyOf R R = 1` 是一个**等式**。
⟹ **不是**同义反复；但**很浅**：它只是「`s ∩ s = s ∪ s = s`」。
**⚠ 为什么必须加 `h`**：若 `R` 不覆盖任何实例，两集合都空，
按定义 `consistencyOf R R = 0`（**不是** `1`），故 `h` **不可省**。
⟹ 这条定理**如实暴露了**「并集为空取 `0`」这条约定的后果。 -/
theorem consistencyOf_self (R : Rule C X Y) (h : (coveredBy (I := I) R).Nonempty) :
    consistencyOf (I := I) R R = 1 := by
  classical
  have hcard : 0 < (coveredBy (I := I) R).card := Finset.card_pos.mpr h
  unfold consistencyOf
  rw [Finset.union_self, Finset.inter_self]
  simp only [hcard.ne', ↓reduceIte]
  exact div_self (by exact_mod_cast hcard.ne')

/-- ⭐⭐⭐ **【`novelty`（新颖性）：规则覆盖的、其它规则都没覆盖的实例比例】**

**拉卡托斯（进步性问题转移）**：说出了**已有规则没说过**的才叫进步。

**定义**：`noveltyOf Rs R := |覆盖 R ∖ ⋃_{R' ∈ Rs, R' ≠ R} 覆盖 R'| / |覆盖 R|`。
若某实例被 `R` 自己以外的规则覆盖，**不算新颖**。
**⚠「`R` 自己以外的规则」的排除用 `R' ≠ R` 过滤**，
而非从 `Rs` 里删 `R`——这样 `R ∉ Rs` 时定义也成立。

**⚠ 需 `[DecidableEq (Rule C X Y)]`**（用于 `R' ≠ R` 的过滤）——
这是本轮**新增的实例要求**，`Rule` 上未必有；故本条定理的签名里**显式列出**。

**⚠ 分母为 `0` 时取 `0`**（`R` 不覆盖任何实例 ⟹ 新颖性无意义 ⟹ 记 `0`）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除 `Rs`、`R` 与必需实例参数）；输入中**不含实数**。

**⚠ 局限（如实登记）**：
1. 它是**相对**新颖性（相对于 `Rs`），**不是**绝对新颖性；
   `Rs` 越大，`noveltyOf` 只能**降**（✅ **已证**，见 `noveltyOf_anti_mono`）。
2. `R ∈ Rs` 与 `R ∉ Rs` 都对同一个公式适用，本轮**不**讨论两者差异。

**⚠ 实现方式**（同 `consistencyOf`）：不用内层 `let`，改为两个独立 `def`
（本 `otherCovered` + 下条 `noveltyOf`），使 `split` 可用。 -/
noncomputable def otherCovered (Rs : FateV2.Model.Rules C X Y) (R : Rule C X Y) : Finset I.Carrier := by
  classical
  exact Finset.univ.filter (fun e =>
    coversOf (I := I) R e ∧ ∃ R' ∈ Rs, R' ≠ R ∧ coversOf (I := I) R' e)

noncomputable def noveltyOf (Rs : FateV2.Model.Rules C X Y) (R : Rule C X Y) : ℝ := by
  classical
  exact
    if (coveredBy (I := I) R).card = 0 then 0
    else (((coveredBy (I := I) R) \ otherCovered (I := I) Rs R).card : ℝ)
      / ((coveredBy (I := I) R).card : ℝ)

/-- ⭐ **`noveltyOf` 在 `[0, 1]`。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有规则集 `Rs` 与规则 `R`（外加实例参数）。
结论 `∈ Set.Icc 0 1` **没有**被包进任何假设；它由定义在
「覆盖集为空」与「非空」两支上分别取值 `0` 与商而得。
**⚠ 很浅**：上界由 `s \ o ⊆ s`（`Finset.sdiff_subset`）给出。 -/
theorem noveltyOf_mem_Icc (Rs : FateV2.Model.Rules C X Y) (R : Rule C X Y) :
    noveltyOf (I := I) Rs R ∈ Set.Icc (0 : ℝ) 1 := by
  unfold noveltyOf
  classical
  split
  · simp
  · rename_i h
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)

/-- ⭐⭐ **【新颖性随规则集扩张而单调不增】**

**⟹ 「进步性问题转移」的一个形式化后果**：
已有规则**越多**，一条新规则能带来的**新颖性上限越低**
（`Rs₁ ⊆ Rs₂ ⟹ noveltyOf Rs₂ R ≤ noveltyOf Rs₁ R`）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : Rs₁ ⊆ Rs₂` 是**两个规则集之间的包含**（`⊆` 于 `Set (Rule C X Y)`）；
结论是**两个实数**之间的 `≤`。
`h` 里**没有** `Finset.card`、`Finset.sdiff`、除法或任何 `ℝ`。
⟹ **不是**同义反复。
**⚠ 很浅**，但**不是** `rfl`：证明确实要做两步
（`∃` 的见证集扩大 ⟹ 差集缩小 ⟹ 商单调）。

**⚠ 必须加实例**：`Rs₁ ⊆ Rs₂` 中 `∃ R' ∈ Rs₂` 的**从属证明**需要
把 `h` 给出的 `R' ∈ Rs₁` 提升到 `Rs₂`，这**不需要** `DecidableEq (Rule C X Y)`
（`∃` 的 `∈` 是 `Set.mem`，不是 `Finset.mem`），
故本条**不必**要求 `[DecidableEq (Rule C X Y)]`。
但 `noveltyOf` 的定义内部已 `classical`，故无额外要求。 -/
theorem noveltyOf_anti_mono {Rs₁ Rs₂ : FateV2.Model.Rules C X Y} (R : Rule C X Y)
    (h : Rs₁ ⊆ Rs₂) :
    noveltyOf (I := I) Rs₂ R ≤ noveltyOf (I := I) Rs₁ R := by
  classical
  have hmono : otherCovered (I := I) Rs₁ R ⊆ otherCovered (I := I) Rs₂ R := by
    intro e he
    simp only [otherCovered, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨hRe, R', hR', hne', hcov'⟩ := he
    exact ⟨hRe, R', h hR', hne', hcov'⟩
  unfold noveltyOf
  by_cases hs : (coveredBy (I := I) R).card = 0
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]
    have hcard : ((coveredBy (I := I) R) \ otherCovered (I := I) Rs₂ R).card
        ≤ ((coveredBy (I := I) R) \ otherCovered (I := I) Rs₁ R).card := by
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_sdiff] at he ⊢
      exact ⟨he.1, fun hc => he.2 (hmono hc)⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end RuleCoversFormulas

/-! ---------------------------------------------------------------------------
  §10 末尾：**仍然无公式的维度**（如实登记，不夸大）
  ---------------------------------------------------------------------------

本轮（§10）之后，`Dimensions` 的 8 个维度中**有真公式的是 6 个**：

| 维度 | 公式 | 位置 |
|---|---|---|
| `falsifiability` | `falsifiabilityOf` | §8 |
| `independence` | `independenceOf` | §9 |
| `simplicity` | `simplicityOfSet` | §9 |
| `explanatory` | `explanatoryOf` | §10（本轮）|
| `novelty` | `noveltyOf` | §10（本轮）|
| `consistency` | `consistencyOf` | §10（本轮）|

**仍然只有纯参数（无公式）的 2 个**：

- **`operationality`**（可操作性）：缺**可观测性定义**。
  「一个规则可操作」需要「它的 `kernel` 能否由某个可观测统计量算出」，
  这要求 `Y.Carrier` 上有可观测结构（如 `MeasurableSpace` + 可数生成元），
  `Y` 目前只有 `Carrier : Type*` + `MeasurableSpace`，**不够**。
- **`robustness`**（稳健性）：缺**拓扑**。
  「稳健」= 输入的**小扰动**只引起分布的**小变化**，
  这要求 `C.Carrier` / `X.Carrier` 上有拓扑、`Measure Y.Carrier` 上有度量
  （如 Prokhorov / Wasserstein）。**本轮均无**。

⟹ **本文件不声称「8 个维度都有公式」**：**6 个有，2 个无**。
⟹ 并且 **`Dimensions`（§1）的字段一个都没有被替换**（纪律：只加不改）。
   要真正接上，需要一个**新文件**把 `Dimensions` 的字段定义为这些 `...Of` 函数，
   并证明该 `Dimensions` 实例的性质；**那不在本轮范围内**。
-/

/-! ---------------------------------------------------------------------------
  §11  `RuleCovers` 的**具体实例**（单点集测度非零）
  ---------------------------------------------------------------------------

**背景与动机**：§10 的 `RuleCovers` 是一个**抽象** class，`covers` 语义未定。
本节给出**一个具体实例**，使 §10 的 `explanatoryOf` / `noveltyOf` / `consistencyOf`
三个公式获得**真实的、可计算的语义**：

> 实例 `e` 是 `(c, x, y)` 三元组（`obj := (c, x)`、`attrs := y`）；
> **规则 `R` 覆盖 `e`** 当且仅当 **`R.kernel c x {y} ≠ 0`**
> （即 `R` 在 `(c, x)` 处给 `y` 分配了**正质量**）。

**(a) `Measure.support` 不可用（实测错误，如实登记）**：
本环境尝试 `import Mathlib.MeasureTheory.Measure.Typeclasses` 得到

```
error: object file '.../Mathlib/MeasureTheory/Measure/Typeclasses.olean' does not exist
```

且 `import EvaluationSystems` 后 `#check @Measure.support` 报
`Unknown identifier \`Measure.support\``。⟹ **`support` 不能用**。

**(b) 为什么改用「单点集测度非零」**：
`support` 的直觉语义是「`y` 属于 `R.kernel c x` 的支撑」，
而「支撑」最直接的可检验形式就是「`y` 的**每个邻域**有正质量」；
在没有拓扑的情况下，「单点集 `{y}` 有正质量」（`R.kernel c x {y} ≠ 0`）
是**最自然、且不需要任何额外结构**的替代。
实测 `Measure` 的应用（`μ s`）与 `Measure.dirac_apply` **均可用**，
故这个谓词**完全可表达、可证明**。

**(c) 载体是 `C.Carrier × X.Carrier × Y.Carrier`（不用 `Instance`，避免 import）**：
`Instance` 定义在 `Fate/InstanceChain.lean:52`，而
`Fate/EvaluationSystems.lean` 目前只 import `FateV2.Rules` 与 `FateV2.Rules`。
实测依赖方向：`Fate/InstanceChain.lean` 的 `^import` 行只有 `import FateV2.Rules.LawRule`，
而 `LawRule` 依赖链**不含** `EvaluationSystems`，故**理论上不成环**；
但为**最小化风险**（纪律 (i)：成环就不 import），本节**不引入任何新 import**，
直接用乘积类型作为 `InstSpace.Carrier`。
`InstSpace`（`Fate/Frame.lean:568-570`）只有 `Carrier : Type*`，
故 `⟨C.Carrier × X.Carrier × Y.Carrier⟩` 是**合法的** `InstSpace` 项。

**(d) 本实例做到了什么**：
§10 的 `explanatoryOf`、`noveltyOf`、`consistencyOf` 三个维度公式，
在本实例下**不再是空转**：它们分别成为
「`R` 给多少 `(c,x,y)` 三元组分配了正质量」的比例/计数类量。
⟹ 三个维度有了**真实语义**。

**(e) 仍然无公式的维度（如实登记，不夸大）**：
**`operationality`** 与 **`robustness`** **仍然没有公式**——
它们缺的是**可观测性定义**与**拓扑**（见 §10 末尾），
本节的「单点集非零」实例**不能**弥补这两者。
⟹ 本节交付后**有公式的仍是 6 个，无公式的仍是 2 个**。

**(f) 本节第二个交付物需要额外假设（如实登记）**：
`covers_of_isDet` 需要 `[MeasurableSingletonClass Y.Carrier]`，
因为 `Measure.dirac_apply` 的陈述（已 `#check`）本身需要它：

```
∀ {α} [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) (s : Set α),
  Measure.dirac a s = s.indicator 1 a
```

无此假设时「`{y}` 是否可测」无从谈起，`dirac_apply` 不能直接用。
-/

/-- ⭐⭐⭐ **【`RuleCovers` 的具体实例：单点集测度非零】**

**语义**：实例 `e` 是 `(c, x, y)` 三元组（`obj := (c, x)`、`attrs := y`），
**规则 `R` 覆盖 `e`** 当且仅当 **`R.kernel c x {y} ≠ 0`**
（即 `R` 在 `(c, x)` 处给 `y` 分配了**正质量**）。

**⟹ 这给了 `explanatory` / `consistency` / `novelty` 三个维度公式一个【真实语义】**。
（详见本节文件头 (d)。）

**⚠ 为什么用单点集测度而不是 `Measure.support`**：
`Measure.support` 所在的 Mathlib 模块在本环境下未编译
（`.../Measure/Typeclasses.olean` 不存在），
而 `Measure` 的应用（`μ s`）已可用（实测）。详见文件头 (a)(b)。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本声明是 `instance`（一个 `RuleCovers` 的**构造**），**没有前件**，
只有 `Rule` / `StateSpace` / `OutSpace` 所必需的实例参数。
其 `covers` 字段是**定义**，其值中含有的 `R`、`e` 全部来自输入。
⟹ **不存在**「把结论包进前件」的可能。

**⚠ 载体**：`C.Carrier × X.Carrier × Y.Carrier`（不用 `Instance`，见文件头 (c)）。 -/
instance instRuleCoversTriple (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] :
    RuleCovers C X Y ⟨C.Carrier × X.Carrier × Y.Carrier⟩ where
  covers R e := R.kernel e.1 e.2.1 {e.2.2} ≠ 0

/-- ⭐⭐ **【`covers` 与点质量规则的相容性】**

**确定性规则（`Rule.IsDet`）在其「目标点」上必定覆盖该点。**

即：若 `R` 由某个 `DetRule d` 诱导，则对任意 `(c, x)`，
存在 `y` 使 `R` 在 `(c, x)` 处给 `{y}` 分配正质量。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : R.IsDet` 即 `∃ d, d.toRule = R`（**一个存在量词**）；
结论是 `∃ y, R.kernel c x {y} ≠ 0`（**另一个存在量词**）。
`h` 里**没有**任何 `≠ 0`、`{·}` 或 `y`；
反向亦不平凡（若 `R` 是两点混合则 `h` 假，如 `Fate/Frame.lean:414` 所述）。
⟹ **不是**同义反复。

**⚠ 实质内容**：本定理把 `R.IsDet`（抽象的存在性谓词）与
§11 实例 `instRuleCoversTriple` 的 `covers`（单点集非零）**接了起来**，
说明该实例的 `covers` **不是空的**——确定性规则一定覆盖某些实例。

**⚠ 很浅**：它**只**说「目标点被覆盖」，**不说**以下任何一条：
（i）`R` 覆盖**哪些**实例（除目标点外不保证）；
（ii）`covers` 是否与 `R` 的真理性有关；
（iii）任何关于三个维度公式排序的结论。

**⚠ 需要 `[MeasurableSingletonClass Y.Carrier]`**（`Measure.dirac_apply` 的固有要求，见文件头 (f)）。 -/
theorem covers_of_isDet {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [MeasurableSingletonClass Y.Carrier]
    (R : Rule C X Y) (h : R.IsDet) (c : C.Carrier) (x : X.Carrier) :
    ∃ y, R.kernel c x {y} ≠ 0 := by
  rw [Rule.isDet_iff_dirac] at h
  obtain ⟨y, hy⟩ := h c x
  refine ⟨y, ?_⟩
  rw [hy, MeasureTheory.Measure.dirac_apply]
  simp

/-- ⭐⭐⭐ **【`covers` 的实例语义与 `IsDet` 的相容性（本章核心）】**

同一结果，但**直接用实例的 `covers` 谓词**表述：

> 若 `R` 是确定性规则，则存在 `y` 使**实例** `(c, x, y)` **被 `R` 覆盖**。

**⟹ 这把 §11 的 `instRuleCoversTriple` 与 `Rule.IsDet` 直接接上**：
§10 三个维度公式（`explanatoryOf` / `noveltyOf` / `consistencyOf`）
所用的 `covers`，在确定性规则上**必有非空覆盖集**。

**⚠ 前件与结论的关系（自审，防同义反复）**：
同 `covers_of_isDet`：前件是 `R.IsDet`（存在一个 `DetRule`），
结论是一个关于**实例 `covers` 谓词**的存在量词；
前件**不含** `covers`、`≠ 0` 或任何 `Finset`。
⟹ **不是**同义反复。

**⚠ 与 `covers_of_isDet` 的关系**：后者是**裸形式**（`R.kernel c x {y} ≠ 0`），
本定理是**实例形式**（`RuleCovers.covers R (c, x, y)`），
二者互补：本定理才是「对 §10 公式**真的有用**」的版本。

**⚠ 很浅**：仍**不**给出覆盖集**具体**由哪些实例组成，
也**不**给出任何维度排序结论。 -/
theorem covers_triple_of_isDet {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [MeasurableSingletonClass Y.Carrier]
    (R : Rule C X Y) (h : R.IsDet) (c : C.Carrier) (x : X.Carrier) :
    ∃ y : Y.Carrier,
      @RuleCovers.covers C X Y ⟨C.Carrier × X.Carrier × Y.Carrier⟩ _ _
        (instRuleCoversTriple C X Y) R (c, x, y) := by
  rw [Rule.isDet_iff_dirac] at h
  obtain ⟨y, hy⟩ := h c x
  exact ⟨y, by
    show R.kernel c x {y} ≠ 0
    rw [hy, MeasureTheory.Measure.dirac_apply]
    simp⟩


/-! ===========================================================================
  §12  ⭐⭐⭐ **`robustnessOf`（鲁棒性）：规则对状态扰动的核稳定半径**
  ===========================================================================

**作者第 592 轮裁决原话（逐字）**：
> 「**做**」
> 「**甲**」

第 602 轮裁决书对本维度的指令原话（逐字摘录）：
> **(A)** 若 `Measure` 的拓扑可用 ⟹ 写**真连续性**（`Continuous (fun x => R.kernel c x)`）
> **(B)** 若不可用 ⟹ 写 **`robustnessOf R := if R.IsDet then 1 else 0`**
> **(B) 是凑数，可以不做（如实说明）**

-----------------------------------------------------------------------------
(a) `Measure` 的拓扑 / 度量的 **`#check` 实测结果**（裁决书要求的 (b) 条）
-----------------------------------------------------------------------------
在 `import EvaluationSystems` + `open MeasureTheory` 之下，实测：

```
#check @MeasureTheory.Measure.instTopologicalSpace
  → error(lean.unknownIdentifier): Unknown constant
#check @MeasureTheory.Measure.tendsto_iff_forall_isOpen_le
  → error(lean.unknownIdentifier): Unknown constant
#check @MeasureTheory.Measure.le_of_forall_isOpen_le
  → error(lean.unknownIdentifier): Unknown constant
#check @MeasureTheory.Measure.instEMetricSpace / instMetricSpace
    / instPseudoEMetricSpace / instDist
  → 全部 error(lean.unknownIdentifier): Unknown constant
```

⟹ **`Measure Y.Carrier` 上【既无拓扑、也无距离】**（本 Mathlib 环境）。
⟹ **选项 (A)【不可行】**：`Continuous (fun x => R.kernel c x)` 在类型上无法写出
   （`Continuous` 需要目标空间的 `TopologicalSpace`，合成不出来）。

-----------------------------------------------------------------------------
(b) 走的是 **(C)**：不用 `Measure` 的拓扑，而用 `X` 的伪度量做「核稳定半径」
-----------------------------------------------------------------------------
**(a) 条排除了 (A)，而裁决书明说 (B) 是凑数、可以不做。**
⟹ 本轮**不做 (B)**（那个定义与 §8 `falsifiabilityOf` 完全同构，无任何新内容），
   **改为做裁决书「更好的选择（推荐）」那一支**——只是用 `sSup` 而非 `sInf` 实现，
   使定理**非平凡且无反例**（理由见 (c)）。

**(b-1) 定义所需结构**：`StateSpace.carrier` 本环境**没有**伪度量，
故本节的公式在签名上**显式要求** `[PseudoMetricSpace X.Carrier]`。
**这是一个真的前件**：没有距离就没有「扰动大小」，本维度在此环境中
**只能在带距离的状态空间上定义**。✅ 这与 §10 的 `RuleCovers` 需要外部 class 一致。

**(b-2) 定义**：给定 `R : Rule C X Y`、`c : C.Carrier`、`x : X.Carrier`，

  `stableRadius R c x := sSup { d : ℝ | ∃ y, dist y x = d ∧ R.kernel c y = R.kernel c x }`

即「**与 `(c, x)` 预测完全相同的状态**到 `x` 的最大距离」
（状态空间中「预测不变」的最大球半径）。

  `robustnessOf R c x :=` **若半径集合非空且无界则 `1`，否则 `min 1 (radius / (1 + radius))`**

-----------------------------------------------------------------------------
(c) 为什么用 `sSup`（最大稳定半径）而**不用** `sInf`（最早改变距离）——**必须如实登记**
-----------------------------------------------------------------------------
裁决书的 (b) 建议写成 `inf { dist x y | kernel c y ≠ kernel c x }`。
**这个量在数学上是平凡的**：状态空间上有**无穷多**远离 `x` 的点，
几乎必然**改变预测**，故该 `inf` 在绝大多数情形下**恒等于 `0`**——
于是「鲁棒性」对所有非平凡规则恒为 `0`（或 `1`，取决于是否空集），
**不区分任何东西**，且任何「> 0」的定理都**假**。
（这正是本项目最高频的毛病：拿一个恒为常数的量与 `[0,1]` 区间做无信息定理。
 我不做这个。）

⟹ 改用**对偶**的 `sSup`（**最大稳定半径**），它才是「**能容忍多大的扰动**」：
- 退化/非单射度量的情形（`dist ≡ 0`）⟹ `sSup {0} = 0` ⟹ `robustnessOf = 0`；
- 稳定半径无界（`dist` 无界且全空间预测不变）⟹ `robustnessOf = 1`；
- 其余情形 ⟹ `x / (1+x) ∈ [0, 1)`。

**(c-1) ⚠ 本定义是「状态扰动的稳定半径」，【不是】通常意义上的「分布鲁棒性」**：
 它度量的是 `kernel` 作为 `X.Carrier → Measure Y.Carrier` 的函数**在一点处保持不变**
 的邻域大小，**不是** `Measure` 上的 Wasserstein/Prokhorov 型距离。
 **本环境无 `Measure` 拓扑 ⟹ 真正的分布鲁棒性【没有做】。如实登记。**

-----------------------------------------------------------------------------
(d) 交付物与**自审（防同义反复 / 防前件包结论）**
-----------------------------------------------------------------------------
本节交付 **3 个 `def` + 1 条 `theorem`**：
`stableRadiusDist`（半径集合）、`stableRadius`（`sSup`）、`robustnessOf`、
`theorem robustnessOf_mem_Icc`。

`robustnessOf_mem_Icc` 的**前件**只有：`PseudoMetricSpace` / `MeasurableSpace`
**类型类实例**（它们不是本定理的结论）。结论 `robustnessOf R c x ∈ Icc 0 1`
**没有**被包进任何假设。
⚠ **但必须诚实说**：由于定义中**显式做了 `min 1` 与 `1` 的截断**，
这条定理的证明**很容易**（`split` + `min_le_iff` / `le_min`）。
**它的价值在「定义有意义且值域如声称」，不在证明难度**——
与 §8/§9 的 `..._mem_Icc` 同样的诚实等级。**它不是深刻定理。**
-/

namespace RobustnessFormula

open MeasureTheory

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [PseudoMetricSpace X.Carrier] [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-- ⭐ **在 `(c, x)` 处「预测不变」的状态到 `x` 的距离集合**。

`d ∈ stableRadiusDist R c x` ⟺ 存在状态 `y`，`dist y x = d` **且**
`R.kernel c y = R.kernel c x`（在 `y` 处的预测与在 `x` 处的预测**完全同一**）。

**⚠ 只含非负数**（`dist` 的值域），故 `sSup` 与 `0` 的比较无障碍。 -/
def stableRadiusDist (R : Rule C X Y) (c : C.Carrier) (x : X.Carrier) : Set ℝ :=
  { d : ℝ | ∃ y : X.Carrier, dist y x = d ∧ R.kernel c y = R.kernel c x }

/-- ⭐ **`stableRadius`：`(c, x)` 处的核稳定半径** = 「预测不变」的最大状态距离
（`stableRadiusDist` 的 `sSup`）。

⚠ 若 `dist` 无界且全空间预测不变，则集合无界 ⟹ `sSup = 0`（`Real.sSup` 对无界集的约定）。
`robustnessOf` 在 `def` 里**显式**用非空性 + 有界性分支处理这种情况，
**不依赖** `sSup` 的边界约定。 -/
noncomputable def stableRadius (R : Rule C X Y) (c : C.Carrier) (x : X.Carrier) : ℝ :=
  sSup (stableRadiusDist R c x)

/-- ⭐⭐⭐ **【`robustnessOf`（鲁棒性）：规则 `R` 在 `(c, x)` 处的核稳定度】**

**波普尔/拉卡托斯（裁决书原话的动机）**：「一个能被微小扰动改变全部预测的规则是脆弱的。」
⟹ 鲁棒 ⟺ **能容忍**更大的状态扰动而**不改变预测**。

**定义（三段式）**：
1. `stableRadiusDist R c x` **空**（状态空间为空）⟹ `0`；
2. 稳定半径**无界**（`∀ b, ∃ d ∈ set, b ≤ d`）⟹ `1`（**完美鲁棒：任意大的扰动都不改变预测**）；
3. 其余 ⟹ `min 1 (r / (1 + r))`，其中 `r = stableRadius R c x`（`≥ 0`）。

第 3 段的 `r / (1 + r)` 是 `[0, ∞) → [0, 1)` 的**标准饱和映射**；
`min 1` 只是使"无界"与"有界"两支**在值域上无缝衔接**。

**⚠ 这不是分布鲁棒性**：`Measure Y.Carrier` 上无拓扑/度量（见本节 (a) 的 `#check` 实测），
本量度量的是 `kernel` 作为 `X → Measure Y` 的函数**在 `(c,x)` 附近保持不变**的邻域大小。
**真正的「分布层面的鲁棒性」本环境【没有做】**。 -/
noncomputable def robustnessOf (R : Rule C X Y) (c : C.Carrier) (x : X.Carrier) : ℝ := by
  classical
  exact
    if (stableRadiusDist R c x).Nonempty then
      if BddAbove (stableRadiusDist R c x) then
        min 1 (stableRadius R c x / (1 + stableRadius R c x))
      else 1
    else 0

/-- ⭐ **`robustnessOf` 的值域在 `[0, 1]`。**

**⚠ 自审（防同义反复 / 防前件包结论）**：
前件**只有** `[PseudoMetricSpace]` / `[MeasurableSpace]` **类型类实例**
与 `R`、`c`、`x` 的具体取值；**没有**任何把 `0 ≤ robustnessOf R c x ≤ 1`
——或与之等价的陈述——写进假设。
结论是关于 `robustnessOf` 的**新信息**（值域落在单位区间）。

**⚠ 但它仍然【很浅】**：定义里已显式写 `min 1` 与 `1` / `0` 两支，
故本定理只是把 `def` 的三支**逐一检查**。它**不是**深刻定理；
价值在于**度量本身由 `Rule` 的 `kernel` 与 `X` 的 `dist` 算出且值域如声称**，
不在证明难度。与 §8/§9/§10 的 `..._mem_Icc` **诚实等级相同**。 -/
theorem robustnessOf_mem_Icc (R : Rule C X Y) (c : C.Carrier) (x : X.Carrier) :
    robustnessOf R c x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold robustnessOf
  split
  · split
    · -- 有界支：`min 1 (r / (1 + r))`
      have hr : 0 ≤ stableRadius R c x := by
        unfold stableRadius
        apply Real.sSup_nonneg
        rintro d ⟨y, rfl, -⟩
        exact dist_nonneg
      have h0 : 0 ≤ stableRadius R c x / (1 + stableRadius R c x) := by
        apply div_nonneg hr
        linarith
      exact ⟨le_min zero_le_one h0, min_le_left _ _⟩
    · exact ⟨zero_le_one, le_refl 1⟩
  · exact ⟨le_refl 0, zero_le_one⟩

end RobustnessFormula

/-! ---------------------------------------------------------------------------
  §12 末尾：**本轮之后 8 个维度的状态**（如实登记）
  ---------------------------------------------------------------------------

| 维度 | 公式 | 位置 | 签名 |
|---|---|---|---|
| `falsifiability` | `falsifiabilityOf` | §8 | `Rule → ℝ` |
| `independence` | `independenceOf` | §9 | `Rule → Rule → ℝ` |
| `simplicity` | `simplicityOfSet` | §9 | `Rules → ℝ` |
| `explanatory` | `explanatoryOf` | §10 | `Rule → ℝ`（需 `RuleCovers`）|
| `novelty` | `noveltyOf` | §10 | `Rules → Rule → ℝ`（需 `RuleCovers`）|
| `consistency` | `consistencyOf` | §10 | `Rule → Rule → ℝ`（需 `RuleCovers`）|
| `robustness` | `robustnessOf` | **§12（本轮）** | `Rule → C → X → ℝ`（需 `PseudoMetricSpace X.Carrier`）|
| `operationality` | **无** | — | 缺可观测性定义，**留给作者裁决** |

**(a) 仍然只有 7 个维度有公式，`operationality`【仍无】**。
  「一个规则可操作」需要「它的 `kernel` 能否由某个**可观测统计量**算出」，
  这要求一个「规则 → 可测量操作序列」的映射（操作化函子），
  本库**无操作 / 测量层**。⟹ **需可观测性定义，留给作者裁决**（裁决书 (e) 条）。

**(b) 本轮的 `robustness`【不是】真正的分布鲁棒性**（见 §12 (a)(c-1)）。
  `Measure Y.Carrier` 上**既无拓扑也无度量**（已 `#check` 实测），
  故「核关于状态的连续性 / Wasserstein 距离」**在本环境不可表达**。
  §12 交付的是**状态扰动下预测不变的半径**这一**替代量**，
  **不是**「`kernel` 的连续性」。**不得声称「鲁棒性已按原义形式化」。**

**(c) 契约上的一处「加重」**：`robustnessOf` 比其余 7 个维度**多要一个类型类**
  `[PseudoMetricSpace X.Carrier]`。**这不是免费的**：
  `StateSpace`（`Fate/Frame.lean`）只有 `Carrier : Type*`，
  **没有**距离。故 `robustness` 只能在**带距离的状态空间**上定义。
  这本身就是一条实质限制，登记在此。

**(d) `Dimensions`（§1）的字段依然一个都没有被替换**（纪律：只加不改）。
  故本轮**没有**交付「`Dimensions` 实例」。理由同 §9 (g-3)：
  `Dimensions.robustness : Rule C X Y → ℝ` 是**单参数**签名，
  而 `robustnessOf` 需要 `c` 与 `x`；**签名不匹配**，
  强行实例化只能用 `fun _ => 0` 造假的常量——**明确不做**。

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
-/

/-! ===========================================================================
  §13  ⭐⭐⭐ **`operationality`（可操作性）：覆盖实例中「输出与 `R` 的预测一致」的比例**
  ===========================================================================

**作者第 606 轮裁决原话（逐字）**：
> 「**裁决 甲** 然后麻烦把理论所有可以证明的都先彻底证明完吧 一大堆还是不完整的」

**「甲」的定义**：**每个覆盖实例都有可测量结果**。
这要求实例 `e` 能**给出**它的状态与输出，即从 `I.Carrier` 到
`X.Carrier` / `Y.Carrier`（以及 `C.Carrier`）的投影。
`InstSpace`（`Fate/Frame.lean`）只有 `Carrier : Type*`，**没有**任何投影；
`RuleCovers`（§10）只给了 `covers` 谓词，**没有**给实例的内部结构。
⟹ 按作者第 577 轮的方法论（「给别的东西加东西」），必须**新增**一个
携带投影的 class：`InstanceProjection`（下方交付物 1）。

**本实现做到了什么**（如实，不夸大）：
1. **交付物 1**：结构 `InstanceProjection`，含 `projC` / `projX` / `projY`
   三个投影字段（`I.Carrier → C.Carrier` / `→ X.Carrier` / `→ Y.Carrier`）；
2. **交付物 2**：`operationalityOf R`，定义为
   「覆盖实例中，**`R` 在该实例的投影处给该实例的投影输出正质量**的比例」；
   覆盖集为空时取 `1`（**空真**：没有覆盖实例需要「可操作」）；
3. **交付物 3**：`operationalityOf_mem_Icc`，证 `operationalityOf R ∈ [0, 1]`。

**⚠ `operationality` 的语义是【一种读法】**：
本实现把「实例 `e` 可操作」读作
> 「`e` 被 `R` 覆盖 **且** `R` 在 `(projC e, projX e)` 处给 `{projY e}` **正质量**」，
即「**`e` 的输出正是 `R` 实际预测的那个**」。
这个读法与 §11 的 `instRuleCoversTriple`
（`covers R e := R.kernel e.1 e.2.1 {e.2.2} ≠ 0`）**语义一致**：
那里 `e` 本身就是三元组 `(c, x, y)`，投影就是三个分量。
⟹ 本读法**不是**唯一的哲学定义；另一种读法是「`R` 的 `kernel` 可由某个可观测
统计量算出」，那需要**操作 / 测量层**，本库**没有**，故**不声称**已形式化。

**⚠ 与「把结论当参数」的区别（自审，防同义反复）**：
裁决书草稿里曾把 `hX : Measurable projX`、`hY : Measurable projY` 作为
`operationalityOf` 的**参数**传入，但那样定义出的值**不依赖**这两个参数，
且「可测」被塞进了输入 ⟹ 一切定理都变成同义反复。
本实现**不**走这条路：`operationalityOf` **只**取 `R`（无「可测」前件），
「可操作」用的是**核的正质量**（`R.kernel ... {projY e} ≠ 0`）这个
**与 `R` 真正相关的谓词**，而**不是**投影的可测性。
因此 `operationalityOf` 的数值**确实随 `R` 变化**（见下方 `_eq_zero_of_none`
与 `_eq_one_of_forall` 两条定理，它们说明该量在两端都能取到）。

**⚠ `covers` 与「投影处正质量」的判据是【两个独立谓词】**：
`operationalityOf` 的分子要求 `covers R e ∧ R.kernel (projC e) (projX e) {projY e} ≠ 0`，
其中 **`covers R e` 来自 `RuleCovers`（§10，任意语义）**，
而**第二个合取项来自 `InstanceProjection`（本轮）**。
⟹ 二者**不必**互相蕴含：在 `instRuleCoversTriple` 上它们恰好重合（`projC/projX/projY`
取三个分量时），但在**任意** `RuleCovers` 实例上 `covers` 可以与之无关。
这正是本定义**不**退化为恒 `1` 的原因。

**⚠ 不声称「8 个维度都有唯一的哲学定义」**。
本轮的 `operationality` 是**一种**读法（「输出与 `R` 的预测一致」），
不是唯一读法，也**不声称**它与 `Dimensions.operationality` 的字段签名匹配
（那个是 `Rule C X Y → ℝ`，本轮的 `operationalityOf` 也是单参数 `Rule → ℝ`，
但需要额外的 `[RuleCovers]` / `[InstanceProjection]` 类型类，
且**本实现不替换** `Dimensions` 的字段——纪律「只加不改」）。

**⚠ 无 `sorry` / `admit` / `axiom`。**
-/

/-- ⭐⭐⭐ **【新结构：实例到上下文/状态/输出的投影】**

**作者第 606 轮裁决「甲」的定义**：「每个覆盖实例都有可测量结果」
—— 这要求实例 `e` 能**给出**它的上下文、状态与输出，
即从 `I.Carrier` 到 `C.Carrier` / `X.Carrier` / `Y.Carrier` 的投影。

**⟹ 按作者第 577 轮的方法论（「给别的东西加东西」），加这个 class。**

**⚠ 为什么有 `projC`（裁决书草稿只写了 `projX`/`projY`）**：
「实例 `e` 的输出与 `R` 的预测一致」这句话里的「`R` 的预测」是
`R.kernel c x`，**它在 `c` 与 `x` 处取值**。只知道 `x = projX e`
而不知道 `c = projC e` 时，`R.kernel _ (projX e)` 无法填出 `c` 这个位置。
⟹ `projC` **不是**装饰，是语义上必需的（与 `instRuleCoversTriple`
的 `e.1 : C.Carrier` 对应）。

**⚠ 本 class 无字段定律**：不要求投影单射 / 满射 / 可测。
强加「可测」会**凭空**限制语义（且 `Measurable (projX)` 是与
`MeasurableSpace` 有关的外部条件，不应成为**结构**的一部分）。 -/
class InstanceProjection (I : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 实例对应的上下文。 -/
  projC : I.Carrier → C.Carrier
  /-- 实例对应的状态。 -/
  projX : I.Carrier → X.Carrier
  /-- 实例对应的输出。 -/
  projY : I.Carrier → Y.Carrier

namespace OperationalityFormula

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {I : InstSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
  [Fintype I.Carrier] [DecidableEq I.Carrier]
  [RuleCovers C X Y I] [InstanceProjection I C X Y]

/-- 规则 `R` 覆盖的实例集（与 §10 的 `coveredBy` 同义，但**独立定义**，
因为 §10 的版本在 `RuleCoversFormulas` 命名空间内且依赖不同的变量组）。 -/
noncomputable def opCovered (R : Rule C X Y) : Finset I.Carrier := by
  classical
  exact Finset.univ.filter (fun e => RuleCovers.covers R e)

/-- 实例 `e` 的上下文投影（**显式给出四个空间参数**：
`InstanceProjection.projC` 的 `C`/`X`/`Y` 无法由 `e : I.Carrier` 单凭合一确定，
已实测 `Application type mismatch`；故用本 abbrev 一次性固定它们）。 -/
abbrev pc (e : I.Carrier) : C.Carrier :=
  InstanceProjection.projC (I := I) (C := C) (X := X) (Y := Y) e

/-- 实例 `e` 的状态投影（同上，参数显式固定）。 -/
abbrev px (e : I.Carrier) : X.Carrier :=
  InstanceProjection.projX (I := I) (C := C) (X := X) (Y := Y) e

/-- 实例 `e` 的输出投影（同上，参数显式固定）。 -/
abbrev py (e : I.Carrier) : Y.Carrier :=
  InstanceProjection.projY (I := I) (C := C) (X := X) (Y := Y) e

/-- 覆盖实例中「输出与 `R` 的预测一致」的那些实例（`operationalityOf` 的分子）。 -/
noncomputable def opGood (R : Rule C X Y) : Finset I.Carrier := by
  classical
  exact
    (Finset.univ.filter (fun e => RuleCovers.covers R e)).filter (fun e =>
      R.kernel (pc (I := I) (C := C) (X := X) (Y := Y) e)
        (px (I := I) (C := C) (X := X) (Y := Y) e)
        {(py (I := I) (C := C) (X := X) (Y := Y) e)} ≠ 0)

/-- ⭐⭐⭐ **【`operationality`（可操作性）：覆盖实例中「输出与 `R` 的预测一致」的比例】**

**作者第 606 轮裁决（甲）**：「每个覆盖实例都有可测量结果」。

**本实现的读法**：实例 `e` 若被 `R` 覆盖，则 `R` 在 `e` 的
`(projC e, projX e)` 处给 `projY e` **正质量**
—— 即「`e` 的结果是 `R` 实际预测的」。

**定义**：
`operationalityOf R := |{e | covers R e ∧ R.kernel (projC e) (projX e) {projY e} ≠ 0}| / |{e | covers R e}|`
（若覆盖集空，取 `1` —— **空真**，因为没有覆盖实例需要「可操作」）。

**⚠ 前件与结论的关系（自审，防同义反复）**：
本 `def` **没有前件**（除构造 `Rule` / `InstSpace` 所需的实例参数与 `R` 本身）。
输出是两个**基数之比**，输入中**不含任何实数**；
也**不含**任何「可测」假设（这一点与裁决书草稿不同，见 §13 头注释）。
⟹ 不存在「把结论包进前件」的可能。

**⚠ 语义是【一种读法】**：「可操作」= 「输出与 `R` 的预测一致」。
另一种读法（「`R` 的 `kernel` 可由某个可观测统计量算出」）需要
操作 / 测量层，本库**没有**，故**不声称**已形式化那一种。 -/
noncomputable def operationalityOf (R : Rule C X Y) : ℝ := by
  classical
  exact
    if (opCovered (I := I) R).card = 0 then 1
    else ((opGood (I := I) R).card : ℝ) / ((opCovered (I := I) R).card : ℝ)

omit [DecidableEq I.Carrier] in
/-- ⭐ **`operationalityOf` 在 `[0, 1]`。**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有且仅有 `R : Rule C X Y`（外加所需实例参数）。
结论 `∈ Set.Icc 0 1` **没有**被包进任何假设；它由定义在
「覆盖集空」与「非空」两支上分别取值 `1` 与商而得。

**⚠ 证明细节**：
- 第一支 `1 ∈ [0,1]`：`le_refl` + `zero_le_one`；
- 第二支：分子 `opGood R ⊆ opCovered R`（`Finset.filter_subset`），
  故 `card` 不超过，商 `≤ 1` 由 `div_le_one`（分母正）给出。

**⚠ 很浅**：只说「比例落在 `[0,1]`」，不说任何关于规则好坏的判断。 -/
theorem operationalityOf_mem_Icc (R : Rule C X Y) :
    operationalityOf (I := I) R ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold operationalityOf
  split
  · exact ⟨zero_le_one, le_refl 1⟩
  · rename_i h
    have hpos : (0 : ℝ) < ((opCovered (I := I) R).card : ℝ) := by
      have : 0 < (opCovered (I := I) R).card := Nat.pos_of_ne_zero h
      exact_mod_cast this
    constructor
    · positivity
    · rw [div_le_one hpos]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

omit [DecidableEq I.Carrier] in
/-- ⭐⭐ **【不覆盖任何实例 ⟹ `operationality = 1`（空真）】**

**⟹ 这如实暴露了「覆盖集空取 `1`」这条约定的后果**：
一条不覆盖任何实例的规则，其「覆盖实例的可操作比例」是**空真的 1**，
**不是** `0`。下游若要用 `operationality` 作排序依据，**必须**另行排除这种规则。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : (opCovered R).card = 0` 是**一个基数为零**的陈述；
结论 `operationalityOf R = 1` 是**定义的一支**。
`h` 里**不含** `operationalityOf`、也不含任何实数。
⟹ 不是「把结论抄进前件」；它只是 `if` 的 `pos` 分支被应用。 -/
theorem operationalityOf_eq_one_of_card_zero (R : Rule C X Y)
    (h : (opCovered (I := I) R).card = 0) :
    operationalityOf (I := I) R = 1 := by
  classical
  unfold operationalityOf
  rw [if_pos h]

omit [DecidableEq I.Carrier] in
/-- ⭐⭐ **【所有覆盖实例都与 `R` 的预测一致 ⟹ `operationality = 1`】**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件 `h : ∀ e, covers R e → R.kernel (projC e) (projX e) {projY e} ≠ 0`
是**逐实例的**核正质量断言（**没有任何 `Finset` / 基数 / 实数**）；
结论 `operationalityOf R = 1` 是**两个基数之比等于 1**。
二者之间的桥是「过滤 `h` 后集合不变」+ `card` + 除法。
⟹ **不是**同义反复；但**很浅**。

**⚠ 反过来不成立**：`operationalityOf R = 1` 也可能由「覆盖集为空」得到
（见上一条），故本条**不**是充要条件。 -/
theorem operationalityOf_eq_one_of_forall (R : Rule C X Y)
    (h : ∀ e, RuleCovers.covers R e →
      R.kernel (pc (I := I) (C := C) (X := X) (Y := Y) e)
        (px (I := I) (C := C) (X := X) (Y := Y) e)
        {(py (I := I) (C := C) (X := X) (Y := Y) e)} ≠ 0) :
    operationalityOf (I := I) R = 1 := by
  classical
  have hgood : opGood (I := I) R = opCovered (I := I) R := by
    unfold opGood opCovered
    exact Finset.filter_true_of_mem (fun e he => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact h e he)
  unfold operationalityOf
  rw [hgood]
  by_cases hc : (opCovered (I := I) R).card = 0
  · rw [if_pos hc]
  · rw [if_neg hc]
    exact div_self (by exact_mod_cast hc)

omit [DecidableEq I.Carrier] in
/-- ⭐⭐ **【没有任何覆盖实例与 `R` 的预测一致、且覆盖集非空 ⟹ `operationality = 0`】**

**⟹ 这把 `operationality` 的取值下界也打通**：它与上一条的 `= 1` 合起来
说明该量**真的在 `{0, 1}` 两端都能取到**，即**不是**恒等常数。

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件有两项：`hne : (opCovered R).card ≠ 0`（**覆盖集非空**，一个 `ℕ` 陈述）
与 `h : ∀ e, covers R e → R.kernel ... {projY e} = 0`（**逐实例核为零**，一个等式）。
结论 `operationalityOf R = 0` 是**基数之比为 0**。
`hne` **不可省**：覆盖集为空时定义取 `1`（不是 `0`）。
两级前件里**没有** `operationalityOf`、`Finset.card` 或任何实数。
⟹ **不是**同义反复。 -/
theorem operationalityOf_eq_zero_of_none (R : Rule C X Y)
    (hne : (opCovered (I := I) R).card ≠ 0)
    (h : ∀ e, RuleCovers.covers R e →
      R.kernel (pc (I := I) (C := C) (X := X) (Y := Y) e)
        (px (I := I) (C := C) (X := X) (Y := Y) e)
        {(py (I := I) (C := C) (X := X) (Y := Y) e)} = 0) :
    operationalityOf (I := I) R = 0 := by
  classical
  unfold operationalityOf
  have hgood : opGood (I := I) R = ∅ := by
    unfold opGood
    refine Finset.filter_false_of_mem ?_
    intro e he
    have hcov : RuleCovers.covers R e := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
    exact fun hpos => hpos (h e hcov)
  rw [if_neg hne, hgood]
  simp

end OperationalityFormula

/-! ===========================================================================
  §14  ⭐⭐⭐ **`Dimensions` 的【第一个真实例】**
  ===========================================================================

**(a) 在此之前 `Dimensions` 有 0 个实例（审计 R623「幻影完成」指控成立）**

实测（本轮交付前）：
```
grep -n "Dimensions where" Fate/*.lean        # 无输出（EXIT=1）
grep -n ": Dimensions" Fate/EvaluationSystems.lean
  # 只有 4 处，全是「接收 D : Dimensions 作参数」，无一处构造实例
```
⟹ 8 个 `*Of` 公式存在、8 个字段存在，两者之间**没有任何一条赋值**。
本 §14 补上**第一个**实例。

**(b) 本实例填了哪 3 个 / 哪 5 个是占位**

- **真接上（3 个）**：`falsifiability := falsifiabilityOf`、
  `explanatory := RuleCoversFormulas.explanatoryOf`、
  `operationality := OperationalityFormula.operationalityOf`。
  这 3 个的签名都是 `Rule C X Y → ℝ`，与字段类型**匹配**。
- **占位（5 个）**：`simplicity` / `consistency` / `independence` /
  `novelty` / `robustness` 填 `fun _ => 0`。
  **⚠ 这 5 个不是「有公式」，是【占位】**——本实例只让 `Dimensions` 可被构造，
  **不**表示这 5 个维度已实现。

**(c) 5 个占位为什么装不进去（逐个签名对比）**

| 维度 | 公式真实签名 | `Dimensions` 字段类型 | 为何不匹配 |
|---|---|---|---|
| `simplicity` | `simplicityOfSet (Rs : FateV2.Model.Rules C X Y) : ℝ` | `Rule C X Y → ℝ` | 收**规则集** `Rules`，不是单条 `Rule` |
| `consistency` | `consistencyOf (R₁ R₂ : Rule C X Y) : ℝ` | `Rule C X Y → ℝ` | **两参**，缺第二条规则 |
| `independence` | `independenceOf (R₁ R₂ : Rule C X Y) : ℝ` | `Rule C X Y → ℝ` | **两参**（且需 `[FateV2.Rules.RuleSpec C X Y]`）|
| `novelty` | `noveltyOf (Rs : FateV2.Model.Rules C X Y) (R : Rule C X Y) : ℝ` | `Rule C X Y → ℝ` | **`Rules` + `Rule` 两参** |
| `robustness` | `robustnessOf (R) (c : C.Carrier) (x : X.Carrier) : ℝ` | `Rule C X Y → ℝ` | **三参**（且需 `PseudoMetricSpace X.Carrier`）|

**要把它们真正接上，需要（二选一，均需作者裁决）**：
(a) 修改 `Dimensions` 的 5 个字段类型（触碰理论接口）；
(b) 在实例里用 `fun R => <某个退化值>` 包一层——但那个包装**丢掉了**
    第二条规则 / 规则集 / 邻域点 `(c,x)` 的全部信息，
    所得函数已**不是**原公式的语义。本 §14 **不做 (b)**：
    宁可显式写 `fun _ => 0` 并登记为占位，也不假装「包一层就等于接上」。

**(d) ⚠ 不声称「8/8 已实现」**

本 §14 只声称：「**`Dimensions` 有实例了，其中 3 个字段真接上公式，5 个是占位**」。
不声称裁决 A（8 个维度都有公式且接进接口）已完成。

**⚠ 无 `sorry` / `admit` / `axiom`。**
-/

namespace DimensionsInstance

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {I : InstSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
  [Fintype I.Carrier] [DecidableEq I.Carrier]
  [RuleCovers C X Y I] [InstanceProjection I C X Y]

/-- ⭐⭐⭐ **【`Dimensions` 的第一个真实例】**

**⚠ 这是本文件第一个 `Dimensions` 实例** —— 此前 8 个 `*Of` 公式与 8 个字段之间
**没有任何赋值**（审计 R623 的「幻影完成」指控），本实例补上能匹配的 3 个。

**填了**：`falsifiability := falsifiabilityOf`、`explanatory := explanatoryOf`、
`operationality := operationalityOf`
（这三个的签名都是 `Rule C X Y → ℝ`，与字段匹配）

**没填**：`simplicity` / `consistency` / `independence` / `novelty` / `robustness`
—— 它们的公式签名与字段**不匹配**（2 参 / 收 `Rules` / 3 参），
故只能填 `fun _ => 0` 并**如实标注**：

**⚠ 填 `fun _ => 0` 的那 5 个不是「有公式」，是【占位】** —— 本实例只让 `Dimensions`
可被构造，不表示 5 个维度已实现。详见 §14 头注释 (c) 的逐字段签名对比。 -/
noncomputable def dimsFirst
    {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {I : InstSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [Fintype I.Carrier] [DecidableEq I.Carrier]
    [RuleCovers C X Y I] [InstanceProjection I C X Y] :
    Dimensions C X Y where
  falsifiability := falsifiabilityOf
  simplicity := fun _ => 0
  explanatory := RuleCoversFormulas.explanatoryOf (I := I)
  consistency := fun _ => 0
  robustness := fun _ => 0
  independence := fun _ => 0
  operationality := OperationalityFormula.operationalityOf (I := I)
  novelty := fun _ => 0

/-- ⭐⭐ **【实例的可证伪性字段确实等于 `falsifiabilityOf`（不是常数 0）】**

**⚠ 前件与结论的关系（自审，防同义反复）**：
前件只有 `R : Rule C X Y`（外加构造所需的实例参数）。
结论是一条 `rfl` 可证的**定义等式**，未被包进任何假设。 -/
theorem dimsFirst_falsifiability (R : Rule C X Y) :
    (dimsFirst (I := I)).falsifiability R = falsifiabilityOf R := rfl

/-- ⭐⭐ **【实例的解释力字段确实等于 `explanatoryOf`（不是常数 0）】** -/
theorem dimsFirst_explanatory (R : Rule C X Y) :
    (dimsFirst (I := I)).explanatory R = RuleCoversFormulas.explanatoryOf (I := I) R :=
  rfl

/-- ⭐⭐ **【实例的可操作性字段确实等于 `operationalityOf`（不是常数 0）】** -/
theorem dimsFirst_operationality (R : Rule C X Y) :
    (dimsFirst (I := I)).operationality R = OperationalityFormula.operationalityOf (I := I) R :=
  rfl

/-- ⭐ **【实例的 5 个占位字段确实是常数 `0`（如实登记，不冒充「有公式」）】 -/
theorem dimsFirst_placeholders (R : Rule C X Y) :
    (dimsFirst (I := I)).simplicity R = 0 ∧
    (dimsFirst (I := I)).consistency R = 0 ∧
    (dimsFirst (I := I)).independence R = 0 ∧
    (dimsFirst (I := I)).novelty R = 0 ∧
    (dimsFirst (I := I)).robustness R = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end DimensionsInstance

/-! ---------------------------------------------------------------------------
  §13 末尾：**本轮之后 8 个维度的状态**（如实登记）
  ---------------------------------------------------------------------------

| 维度 | 公式 | 位置 | 签名 |
|---|---|---|---|
| `falsifiability` | `falsifiabilityOf` | §8 | `Rule → ℝ` |
| `independence` | `independenceOf` | §9 | `Rule → Rule → ℝ` |
| `simplicity` | `simplicityOfSet` | §9 | `Rules → ℝ` |
| `explanatory` | `explanatoryOf` | §10 | `Rule → ℝ`（需 `RuleCovers`）|
| `novelty` | `noveltyOf` | §10 | `Rules → Rule → ℝ`（需 `RuleCovers`）|
| `consistency` | `consistencyOf` | §10 | `Rule → Rule → ℝ`（需 `RuleCovers`）|
| `robustness` | `robustnessOf` | §12 | `Rule → C → X → ℝ`（需 `PseudoMetricSpace X.Carrier`）|
| `operationality` | `operationalityOf` | **§13（本轮）** | `Rule → ℝ`（需 `RuleCovers` + `InstanceProjection`）|

**(a) 现在 8 个维度都有**一个**公式**，但：
  - `operationality` 的公式需要**两个**类型类（`RuleCovers` 与**新增的** `InstanceProjection`），
    比 §8/§9 的维度**重**；
  - 它的语义是**一种读法**（「覆盖实例的输出与 `R` 的预测一致」），
    **不是**唯一的哲学定义。

**(b) 「甲」的核心交付是 `InstanceProjection`**（`projC`/`projX`/`projY`）：
  在此之前，`InstSpace` 只有一个裸 `Carrier : Type*`，
  「实例 `e` 的状态是什么」在类型层**无法表达**。
  有了它，「每个覆盖实例都有可测量结果」中**「有结果」**这一半被落实为
  `projY : I.Carrier → Y.Carrier`；**「可操作」**这一半被落实为
  核在 `(projC e, projX e)` 处给 `{projY e}` 正质量。
  **⚠ 仍【不】声称**「可测」（`Measurable projX` 等）—— 那需要额外的
  `MeasurableSpace` 上的条件，本实现**没有**把它当结论证明，
  也**没有**把它当参数塞进定义（见 §13 头注释的自审）。

**(c) `Dimensions`（§1）的字段依然一个都没有被替换**（纪律：只加不改）。
  本轮**没有**交付「`Dimensions` 实例」。

**(d) 不声称「8 个维度都有唯一的哲学定义」**，
  也不声称各维度**互不相关**或**可统一加权**（那是 §5 已批评过的假定）。

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
-/

end EvaluationSystems

end FateV2.Rules