# 侦察：Lean 代码结构反推出的「这套预测系统到底是什么样」的候选设计

> **视角**：Lean 代码结构（802 个 `.lean`、10,164 条定理、3,147 个定义；按理论层映射的 13 层 + 833 条主定理）。
> **方法**：9 份必读文件逐份读完（模块→层映射 CSV 全 803 行、主定理清单 CSV、主定理路线图全 2159 行、
> L9/L5/L7/L12/L8 五份设计意图、`Fate.lean` 全 1202 行），并对关键模块回读 **Lean 源码本体**核对声明与行号。
> **只摘材料里实际存在的系统形态**，不补设计、不做推导；找不到的宁可不写。
>
> **路径约定**（均相对工作区根 `C:\Users\xingg\Desktop\命运计划\`）：
> - `Fate/*.lean` 全路径为 `命运-素材-原始文件-不可更改/Fate/*.lean`（下文简写 `Fate/模块名.lean`）
> - `映射` = `理论-文档/_扫描/lean设计/模块到理论层映射.csv`
> - `清单` = `理论-文档/_扫描/lean设计/主定理清单.csv`
> - `路线图` = `理论-文档/05-修正清单/主定理路线图.md`
> - `L9` = `理论-文档/_扫描/lean设计/设计意图/L9-世界模型.md`（L1/L2/L5/L6/L7/L8/L10/L11/L12 同构）
>
> **判据**：一条候选必须能独立回答「输入是什么 → 经过哪些部件 → 输出是什么」，且与他条有**结构**差异。
> **因此本清单把「同一堆代码的不同抽象层」也分开列**（例如「六环管线」与「端到端四环」是同一批 `def` 的两种分解），供后续去重。

---

## 0 · 一页纸：20 条候选的族谱

材料（= 代码 + 由代码自动生成的意图摘要）里同时活着**六种互不兼容的「系统主句」**：

| 族 | 主句 | 候选编号 |
|---|---|---|
| **A 世界模型族** | 系统 = 一个**四要件世界模型**（状态/规则集/模拟器/选择器），外挂场景树与择优器 | 1、19、20 |
| **B 循环族** | 系统 = 一个**分类↔因果的双向循环**，只在信息不足时暂停；预测是循环的副产物 | 2、17 |
| **C 管线族** | 系统 = 一条**带残差回写的前向管线**（观测→估计→预测→残差→更新→学习） | 3、4、5 |
| **D 规则族** | 系统 = 一条**规则生成链**（数据→形式背景→规则→Step→轨迹），因果是旁支 | 6、7、8、9 |
| **E 因果族** | 系统 = **SCM 三层级 + 图⟹概率桥**，世界模型只是它的一个实例 | 10、11、12 |
| **F 参数/识别族** | 系统 = 从观测里**反推参数或潜变量**，输出是等价类/区间而非数值 | 13、14、18 |
| **G 元层族（非预测链）** | 系统 = 一套**判据 + 审计 + 裁决**，产出不是预测而是「这条结论能不能信」 | 15、16、17 |

一句话观察：**代码把「层」做全了（13 层、802 模块），但把「链」做断了**——
`Fate.lean` 根 import 了 1202 行，其中 `L9` 世界模型 42 模块、`L10` 裁决 11 模块、`L11` 评估 9 模块**在净版正文里没有任何对应章节**
（净版正文「世界模型」出现 0 次），所以这三层的系统形态**只存在于代码里，不存在于理论文档里**。
反过来说：**本视角能看见的候选，有相当一部分在净版里没有文字依据**——这是本清单与「文档视角」清单最大的结构差异。

---

## 候选 1 · 四要件世界模型 + 场景树 + 策略（作者三能力版）

- **一句话**：整个系统就是「一个世界模型（状态+规则集+模拟器+选择器）」，**配上一条「对每个候选干预方案各跑一条轨迹」的场景树，再用一个 `score` 挑出满足要求的那一条**——三件套逐一对应作者原话里的三项能力。
- **输入**：`Frame`（`X/U/Ν/Θ/Act` 五空间）+ 初始状态 `x₀` + 一族候选干预方案 `plans : Set (ℕ → A)` + 外生 `u`、噪声 `ε`。
- **输出**：被选中的干预方案 `s.plan`（附它的轨迹 `s.traj`）；若树有限非空，则保证存在最优场景。
- **部件链路**（按数据流）：
  1. `WorldState`（状态空间+当前值+初值）/ `WorldRules`（规则**集合**，非单条）/ `WorldRulesθ`（参数化规则集）
  2. `WorldSimulator`（单步机制 `step`）+ `Selector`（`select : Rules → C → X → Rule × 评值`）——四块共用同一 `frame` 作胶水
  3. `WorldModel.sim`：`trajGen` 沿 `step` 迭代出轨迹（**输出是 `Traj ℕ X`，不是测度**）
  4. `ScenarioTree`：对每个 `plan` 各生成一个 `Scenario {plan, traj}`
  5. `Policy.score` + `Policy.choose`（`choose_mem` 保证选自树内）；`Policy.IsOptimal` 是**附加条件**不内建
  6. `exists_optimal_scenario`：有限非空树 ⟹ 存在 `score` 最大者
- **与其它候选的关键区别**：① 唯一一条把「**选择器**」做成**一等字段**的候选（其它候选的择优要么在 `Policy` 里、要么在 `InterventionSelection` 里）；② 唯一一条明确「**分支 = 不同干预方案**（共享同一 `u,ε`），不是不确定性分叉」的候选——代码自己写明「故它就是反事实的」（`WorldScenario.lean:39-40`）。
- **证据**：
  - `Fate/WorldModel.lean:271-320`：`structure WorldModel` 的字段表（`frame` / `ctx` / `state` / `rules` / `simulator` / `selector` / `state_consistent`），并逐字解释「`frame` 为什么不是第五部分」
  - `Fate/WorldScenario.lean:8-17`：「三能力」表（① 信息不断注入 ✅ ② 同时模拟不同分支 🔴缺 `ScenarioTree` ③ 挑出满足要求的干预 🔴缺 `Policy`）
  - `Fate/WorldScenario.lean:21-49`：「分支不是不同轨迹，而是不同干预方案」+ `Scenario`/`Policy` 伪码
  - `Fate/WorldScenario.lean:69-89`、`113-133`：`Scenario`/`ScenarioTree`/`Policy`/`isOptimal`/`exists_optimal_scenario` 实体
  - `清单:830`（`WorldScenario,exists_optimal_scenario`）、`L9:49-72`（模块自述）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`score` 的语义「满足要求」被**显式留空**（`WorldScenario.lean:51-55`：「由作者给出，本节不填」）；无限树的最优性未处理（需紧性）。所以「挑出满足要求的一种干预」在代码里**只有壳，没有判准**。

---

## 候选 2 · 分类↔因果双向主循环（信息不足才临时停）

- **一句话**：系统的主线不是一条链而是一个**不终止的循环**——因果进分类系统提规则、分类反过来修因果；循环里两个方向是「向上抽象」与「向下解构」，**只有在信息不足（会过拟合）时才临时 `paused`**。
- **输入**：当前状态 `LoopState ∈ {running, paused}`、信息层级 `info : ℝ`、噪声尺度 `noise : ℝ`、恢复余量 `margin : ℝ`。
- **输出**：下一步状态（继续抽象/解构，还是暂停）；`paused` 的判据同时被接到「数据支持度」上。
- **部件链路**（按数据流）：
  1. `Level := ℕ`（层号越大越抽象；**层的内容作者要求先不定**，故抽象成 `ℕ`）
  2. `abstractUp n k = n + k`（向上抽象，「它归于何类」）/ `deconstructDown n k = n - k`（向下解构，「它由何构成」）
  3. 「不是细分」的形式化：`abstractUp_gt` / `deconstructDown_lt`（方向相反）+ 双向可逆
  4. `step info noise margin : LoopState → LoopState`：`running` 需 `noise < info`；`paused` 恢复需 `noise + margin < info`
  5. 停判据接数据支持度：`paused_iff_supp_le_threshold`（`MainLoopSupportBridge`）
  6. 「不结束」：状态随信息量变化，不冻结终态
- **与其它候选的关键区别**：① 唯一一条**以「拓扑结构」为主句**的候选（作者原话「改变主线的拓扑结构」）；② 唯一一条把「**停止**」做成核心输出的候选（其余候选都假设一直算下去）；③ 它明确否定「两条路并行/分工」与「循环=无限细分」两种读法。
- **证据**：
  - `Fate/MainLoop.lean:45-80`：作者裁决 O 的逐字引文（「循环：分类反过来修因果」「不结束」「不是细分，是抽象和解构」「没有足够信息…才临时停止」）
  - `Fate/MainLoop.lean:18-41`：`step` 的新设计 + `margin` 三区判定（`margin=0` 退化为常值、`margin<0` 方向反了、`0<margin` 唯一正确区间）
  - `Fate/MainLoop.lean:87-93`：`Level`/`abstractUp`/`deconstructDown` 实体
  - `L7:415-441`：`MainLoopSupportBridge`（`paused_iff_supp_le_threshold` 等 5 条主定理）
  - `清单:450-455`：`step_running_iff` / `step_paused_iff` 等 6 条
- **成熟度**：**完整定义+代码**（但「层」的内容被显式抽象成 `ℕ`，见 `MainLoop.lean:78-79`）。
- **备注（冲突）**：本候选与候选 1/3 结构不相容——若主线是循环，则「观测→…→学习」的一次性管线只是**循环体内的一步**；代码里两者**并列存在、互不引用**（`MainLoop` 只 `import Fate.FCA` / `Fate.Classification`）。

---

## 候选 3 · 六环管线（观测 → 估计 → 预测 → 残差 → 更新 → 学习）

- **一句话**：把世界模型当一条**六环流水线**跑：观测 `y = h x`、由 `y` 反推状态估计、再用参数 `θ` 一步预测、作差得残差、残差经 `φ` 回写参数、迭代使 `θ_n → θ*`。
- **输入**：观测值 `y`、参数初值 `θ₀`、外生 `u`、噪声 `ε`、动作 `a`、步长 `η`。
- **输出**：`θ_n → θ*`（收敛点唯一、且 `θ* ≠ 0` 时极限非零）；附 `n` 步闭式偏差 `θ_n - θ* = (1-η)^n (θ₀-θ*)`。
- **部件链路**（按数据流）：
  1. 环① `pipelineObserve h x = h x`
  2. 环② `pipelineEstimate`（用 `RA14Strong.chooseEstimator`；`h` 单射 ⟹ 无噪观测下估计精确）
  3. 环③ `pipelinePredict x u ε θ a = θ*x + u + ε + a`（`pipelinePredict_separates`：`x≠0` 时换 θ 则预测变）
  4. 环④ `pipelineStep`（= `endToEnd`，**不是另造算子**）：残差 = 观测估计 − 规则预测
  5. 环⑤ 参数变化量 = `η × φ(残差)`（`pipelineStep_diff`）
  6. 环⑥ `pipelineN`（= `endToEndIter`）迭代 → `pipeline_tendsto` / `pipeline_tendsto_unique`
- **与其它候选的关键区别**：① 唯一一条把「**估计环**」单独列为第一等环节的候选（候选 4 的端到端四环里没有估计环）；② 唯一一条每个环都有「正确性 + 非平凡性 + 界」三件套的候选（`pipelineEstimate_error`、`pipelineStep_diff`、`pipeline_tendsto`）。
- **证据**：
  - `L9:1016-1038`：模块自述「**BB3：世界模型六环管线（观测 → 估计 → 预测 → 残差 → 更新 → 学习）**」+ 逐环落点表
  - `Fate/WorldModelPipeline.lean:100-120`（`ObsMap`/`Estimator`/`pipelineObserve`/`pipelineEstimate`/`pipelineObserve_estimate`）
  - `Fate/WorldModelPipeline.lean:152-160`（`pipelinePredict` + 闭式）、`:190-212`（`pipelineStep` = `endToEnd`）、`:283-292`（`pipelineN` = `endToEndIter`）、`:320-343`（`pipeline_tendsto` 端到端主定理）
  - `清单:824-826`
  - `映射:795`（`WorldModelPipeline,L9-世界模型,20,3,28889`）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：六环里「学习」环**没有独立模块**——它由 `pipeline_tendsto` 与 `WorldModelCapstone`（候选 19）两头夹住；`WorldModelPipeline` 自身只到收敛，不含 σ 与误差带。

---

## 候选 4 · 端到端四环（观测 → 预测 → 残差 → 更新）

- **一句话**：四环版最小闭环——由观测 `y` 得 `x̂`、由规则一步预测 `x̂_pred`、作差得残差、残差经 `φ` 回写 `θ`；其价值在于**每一环都能单独陈述正确性与非平凡性**。
- **输入**：`WorldModel W` + 观测 `y` + 当前参数 `θ`。
- **输出**：`θ' = θ + η·φ(x̂_obs − x̂_pred)`；`endToEndIter` 的 `n` 步迭代；不动点判据 `endToEnd_fixed_iff`。
- **部件链路**：
  1. 环节① `observe h y`（估计器 `Y → X`）
  2. 环节② `predFrom W θ u ε a`（= `W.sim` 的一步，`predFrom_eq_sim_succ`）
  3. 环节③ `e2eResidual = x̂_obs − x̂_pred`（`e2eResidual_eq_zero_iff`：残差零 ⟺ 两值相等）
  4. 环节④ `endToEnd`：`θ' = θ + η * φ(残差)`（`endToEnd_apply` 逐位展开）
  5. 迭代 `endToEndIter`（零步恒等、一步 `= endToEnd`、不动点保持）
  6. 正确性/非平凡性并置：`endToEnd_fixed`（残差零 ⟹ θ 不动）/ `endToEnd_moves`（残差非零 ⟹ θ 必改）
- **与其它候选的关键区别**：① 四环节版**没有估计环与学习环**（估计被压进 `observe` 一个 `def`）；② 唯一一条把「**正确性 vs 非平凡性可同时陈述**」写成自检项的候选（`EndToEnd.lean:532`）；③ 「类型分工」是它的卖点（`Y→X`、`X→X`、`Residual X`、`Θ→Θ`）。
- **证据**：
  - `Fate/EndToEnd.lean:98-110`（`observe`）、`:130-144`（`predFrom`）、`:165-175`（`e2eResidual`）、`:203-250`（`endToEnd`）、`:437-445`（`endToEndIter`）
  - `Fate/EndToEnd.lean:502-532`：六条「自检」（环节类型、全链类型「观测值 → θ → θ′」）
  - `L7:1177-1197`（模块自述「端到端串联 0%」的判定 + 五条 `def`）
  - `清单:240-241`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：代码自称「端到端串联 0%」的原始动机是「仓内有四个环节的类型，但没有任何一条定理把它们串成一条链」，本模块补的正是那条链；但**它不含世界模型之外的任何因果/识别内容**（因果接口在候选 10）。

---

## 候选 5 · 可执行数值端到端（一条真实数据 → 一个预测值）

- **一句话**：把上面所有抽象定理**压成一个能跑出数字的实例**：给定 `d=2`、`A = swap2`、`x' = (3,-1)`、`θ₀ = (0,0)`、`η = 1/2`，直接算出**一步预测向量**与它的误差带。
- **输入**：具体数值（观测 `x'`、初值 `θ₀`、步长 `η`、写回算子 `A`、目标真值 `y`）。
- **输出**：一个具体预测向量 `pred1 = (-1/2, 3/2)`、模型输出 `A pred1 = (3/2, -1/2)`、一步误差带 `∀ i, |A pred1 i - x' i| ≤ 3/2`、端到端带 `≤ 3/2 + d`、两步后 `≤ 3/4`。
- **部件链路**：
  1. `Corrects swap2CLM swap2`（**是证明出来的，不是假设**，因为 `swap2 ∘ swap2 = id`）
  2. `wbW` 一步写回 → `pred1`
  3. 模型输出 `A pred1`
  4. 误差带（由 `iterErr_closed` 的**等式**推出）
  5. `n` 步收缩 `(1/2)^n`
- **与其它候选的关键区别**：① 唯一一条**输出是具体数**的候选（其余候选输出是命题或集合）；② 唯一一条把「正确性前件 `Corrects` 变成**可证结论**」的候选（其它候选里 `Corrects` 都是前件）；③ 它同时给出「误差带」而不只是「收敛」。
- **证据**：
  - `Fate/TwoDPrediction.lean:5-35`：任务 T4.2、具体数据、主结果与诚实边界（「既有 `predicts_converges` 只给渐近收敛，不是具体预测值」）
  - `Fate/TwoDPrediction.lean:56-80`：`swap2CLM` / `swap2_involutive` / `corrects_swap2` / `xObs` / `thetaZero`
  - `映射:734`（`TwoDPrediction,L13-未归类,20,1`）
  - `L9:346-375`（`DemoEndToEnd`：同型「μ 世界模型跑 N 步、`norm_num` 出数字」）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：本候选与 `DemoEndToEnd` / `EvalDemo` / `EvalReal` / `FullPipelineDemo` **同型不同实例**（都是「跑出数字」），但只有 `TwoDPrediction` 给出**带误差带的多维**结果；其余是 1 维或标量演示。

---

## 候选 6 · FCA 作主线入口的五段式（α_FCA：实例集 → 形式背景 → 概念格 → DG 基 → 规则）

- **一句话**：整个规则的来源是一条**五段构造链**：实例集经唯一的自由输入 `obs` 变成形式背景，经 `polar/closure` 变成概念格，经伪内涵变成 DG 基，再变成规则（理论），最后装成 α 本体并**逐条兑现五条接口义务**。
- **输入**：`(E, M_FCA, obs : E → 2^{M_FCA})`——`obs` 是**唯一自由的一步**，此后全由它机械导出。
- **输出**：规则集 / 理论 `Th(T_E)` + α 本体 `α_FCA : E → 𝔅(K) × 2^{M_FCA}`，且**五条接口全部成立**（值域正确、可靠、完备、非冗余、有限步可算）。
- **部件链路**：
  1. §1 `AlphaData.ctx`：形式背景 `K_E = (G_FCA := E, M_FCA := M, I(e,m) := m ∈ obs e)`
  2. §2 `polar / closureOp`：概念/概念格（`Encoder.Coherent` 的条件是 `polarDown (attrs x) = objects x`）
  3. §3 `IsPseudoIntent` → `thClosure` / `thIter`（闭包迭代）：**DG 基** `T_E`
  4. §4 `rulesUnionOf`：由 DG 基并出「理论」层
  5. §5 α 本体 + 五条接口（值域正确/可靠/完备/非冗余/有限步可算）
- **与其它候选的关键区别**：① 唯一一条**把「数据」当起点、把「规则」当终点**的候选；② 唯一一条把「**唯一自由参数**」写成显式契约的候选（`obs` 之后零自由度）；③ 与候选 7 **互斥**：同一条 FCA 链，此处是**主线入口**，候选 7 是**分类系统**（作者裁决 N 把主线入口判给了别的路）。
- **证据**：
  - `Fate/AlphaFCAConstruction.lean:6`（阶段：**α 的 FCA 版本 —— 端到端完整构造（实例集 → 形式背景 → DG 基 → 规则）**）
  - `Fate/AlphaFCAConstruction.lean:16-32`（五段箭头图 + 五条接口）
  - `Fate/AlphaFCAConstruction.lean:95-114`（`AlphaData` / `ctx`：「实例即对象」）
  - `L5:452-484`（模块自述 + `mem_dgBasis_iff` / `exists_thIter_eq_thClosure`）
  - `清单:23-24`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：**这条链的「主线入口」资格已被否决**——`L5:50-96`（`Classification` 头）逐字写「**作者裁决 N**：FCA 不再承担主线入口（`enc`），**改作分类系统**」；`Fate/AlphaFCA.lean` 本身**当前不可编译**（`AlphaFCAConstruction.lean:37-41`）。故本候选应读作「**曾经的主线设计**」，与候选 7 一起构成一对互斥解。

---

## 候选 7 · FCA 作分类系统 + 两种目光的抽象/解构循环

- **一句话**：FCA 不再是入口，而是一台**分类机**：同一基底随「目光」（`none/up/down`）在「要素」与「概念」之间切换，向上目光给上位归类、向下目光给内部构成，循环的合法性由「结构态是否同构 / 是否可由有限微调导出」判定。
- **输入**：基底对象 `O`（实例或属性集）+ 当前目光 `Gaze`。
- **输出**：该对象当前呈现为「要素」还是「概念」（`IsElement ↔ ¬ IsConcept`，**没有第三种身份**）；循环判定：平凡循环（同构）/ 非平凡循环（不同构且不可微调导出）。
- **部件链路**：
  1. `Gaze`（`none`/`up`/`down`）+ `Temporal {base, gaze}`（基底与目光分开存）
  2. `gazeUp` ↔ `intent`（上位归类）/ `gazeDown` ↔ `extent`（内部构成）+ `suspend`（悬置）
  3. `IsElement` / `IsConcept` + 核心互释「要素是目光不在场的概念」
  4. `TemporalAction` / `temporalFunctor`（时态化是函子）
  5. 循环：`CycleStructure {S, SIso, Derivable}` → `IsTrivialCycle` / `IsNontrivialCycle`
  6. 停判据：`ShouldStop` / `tauOf` / `ShouldStopAt`（与候选 2 的 `step` 同一套信息/噪声判据）
- **与其它候选的关键区别**：① 唯一一条**输出是「分类身份」而非数值/命题**的候选；② 唯一一条把「**目光**」做成状态机的候选（同一对象两种身份）；③ 与候选 6 互斥（同一个 FCA，两种定位）。
- **证据**：
  - `Fate/Classification.lean:8-9`（裁决 N + 裁决 O：「因果进入分类循环 —— 循环的内容是抽象与解构（两种目光）」）
  - `Fate/Classification.lean:100-134`（`Gaze` / `Temporal` / `gaze_switch_preserves_base`）
  - `Fate/Classification.lean:145-149`（`IsElement` / `IsConcept`；`:159` 断言二者互补、无第三身份）
  - `Fate/Classification.lean:849-876`（`CycleStructure` + 平凡/非平凡循环定义）
  - `Fate/Classification.lean:765`（`ShouldStop`）、`:1398`（`tauOf`）、`:1445`（`ShouldStopAt`）
  - `L5:50-96`
- **成熟度**：**只有骨架**——模块自述逐字承认「本实现给出的只是一个**骨架**」（`Classification.lean:844`），「结构」「同构」「有限参数微调」在原文中都未形式化。
- **备注（冲突）**：`s.plan` 式的循环判据**不含任何概率或因果内容**（75 条主定理多为格论/时序判据）；「因果进入分类循环」这一句在代码里**只落到 `import`，没有落到定理**。

---

## 候选 8 · υ 迭代收窄（信息不断注入 → 规则集/版本空间单调收窄 → 不动点）

- **一句话**：系统的运行方式就是「**持续注入数据，规则集单调收窄**」：每次数据进来用 υ（完善/收窄）更新规则族，收窄到某个不动点为止；「全参与 + 按需激活」是同一件事在规则**依赖图**上的版本。
- **输入**：数据流 `Data : ℕ → Data`（不断注入）+ 初始规则集/版本空间 `x₀`。
- **输出**：单调收窄的规则集序列 `R_t`（`R_{t+1} = υ(Data_t, R_t)`），及其不动点/极限（若收敛）；版本空间版本还给出「边界」与终止性。
- **部件链路**：
  1. `UpsilonOperator.IsCompletion`（`S ⊆ υ D S`、单调、幂等）——`υ` 的代数契约
  2. `upsilonIter υ inj x₀ : ℕ → α`（`x_{t+1} = υ_{inj(t)}(x_t)`）
  3. 两条互不替代的收敛判据：`upsilonIter_limit_fixed` / `upsilonIter_limit_unique`（极限是不动点且唯一）
  4. 规则集侧：`VersionSpace.fromData` / `narrowedBy` / `fine`（候选消除）
  5. 依赖侧：`RuleActivation`「开始全部激活 → 数据进来部分不激活 → 被依赖的立刻重新激活（闭包传播）」
  6. 可判定侧：`SynClosureBounded` / `SynClosureSemiNaive`（闭包迭代的有限步上界）
- **与其它候选的关键区别**：① 唯一一条**主句是「时间」**的候选（输入是流不是样本）；② 唯一一条把「**收窄**」而非「拟合」作为核心动作的候选——输出的是**规则集**而不是参数；③ 与候选 13（θ 学习）方向相反：θ 是**逼近一个真值**，此处是**排除候选**。
- **证据**：
  - `L5:2484-2506`（`UpsilonIteration`：阶段「**『信息不断注入』作为 υ 的迭代**」+ `upsilonIter` 与两条收敛定理）
  - `Fate/UpsilonIteration.lean:122`（`upsilonIter` 实体）
  - `Fate/VersionSpace.lean:82-114`（`VersionSpace` / `Consistent` / `fromData` / `meet` / `narrowedBy` / `fine`）
  - `Fate/RuleActivation.lean:74-102`（`Activation` / `Coherent` / `closure`）、`:259`（`fromData`：由 `dep` 与 `suppressed` 造激活态）
  - `映射:749-750`（`VersionSpace` / `VersionSpaceBoundary`）
- **成熟度**：**完整定义+代码**（但**三处机制分别成模块，没有任何一个模块把它们装成一条链**——这是本候选最弱的一环，属「读法」而非「既有装配」）。
- **备注（冲突）**：`UpsilonIteration` 自己登记了反例：`cex_no_uniform_card_bound`（收窄**未必**有统一基数上界），故「收窄一定终止」在本材料里**已被证伪**。

---

## 候选 9 · 规则核心链（SCM / FCA → LawRule → Step → 轨迹 → 世界模型/端到端）

- **一句话**：规则是系统的**中枢类型**：先由 SCM 或 FCA 的 DG 基生成 `LawRule`（约束集），再由 `IsDirac/IsPoint` 判定能否抽出确定性函数 `DetFun`，抽出的 `Step` 装进 `WorldSimulator`，于是「规则驱动的轨迹」与「世界模型的轨迹」被证明**是同一条**。
- **输入**：`SCM`（`PearlHierarchy.SCM` 的 `(pU, sg)`）或 FCA 的 `dgBasis`。
- **输出**：由规则驱动的整条世界模型轨迹（`trajGen_rule_unique`）以及接进端到端后的不动点判据（`ruleWorldModel_endToEnd_fixed_iff`）。
- **部件链路**：
  1. `SCMLawBridge` / `scmFamily`（SCM ⟹ `LawRule`，分三档）/ `AlphaDataToLawRule.dgToLawRule`（DG 基 ⟹ `LawRule`）
  2. `LawRule C X Y := C → X → Set (Measure Y)`（**规则 = 约束集，不是函数**）；`compose = 逐点取交`
  3. 单点档判定：`IsPoint` / `IsPointDet` / `IsDirac`；`exists_detFun_of_isPointDet` / `extractFun_unique`（**可提取性的充要条件**）
  4. `lawDetToStepGen`：`IsDirac` 规则 ⟹ `Step F`（桥路线甲，含相容定理 `DetFunToStep` 与逆向 `StepToLaw`）
  5. `ruleSimulator` / `wFrame`：把 `Step` 装进 `WorldSimulator` 造出 `W`
  6. `trajGen_rule_unique`（世界模型轨迹 = 规则自己的轨迹）、`ruleWorldModel_endToEnd_fixed_iff`（接端到端）
  7. FCA 侧同构路径：`FcaRuleEntersWorldModel`（`dgBasis` ⟹ `RichLaw` ⟹ 驱动世界模型）
- **与其它候选的关键区别**：① 唯一一条以「**类型层**」为主句的候选——它的输入输出不是数据而是**类型之间的转换**（`LawRule ⟷ Rule ⟷ Step ⟷ Traj`）；② 唯一一条正面处理「**组合语义未定**」的候选（`compose` 有三候选语义：相接/边缘化/并，且被证「四公理不足以唯一确定」，见候选 15 的 `T68` 一节）；③ 与候选 6 共享 FCA 起点，但**终点不同**（此处的终点是 `Step`，候选 6 的终点是 `Th(T_E)`）。
- **证据**：
  - `Fate.lean:1036-1045`（`DetFunToStep` / `StepToLaw` / `LawDetToStepGen` / `RuleEntersWorldModel` / `RuleDrivesEndToEnd` / `FcaRuleEntersWorldModel` 六个 import 连成一串）
  - `Fate/LawRule.lean`（经 `L9:412-450`：`LawRule`/`Rule`/`DetFun`/`IsPoint`/`ComposeCompat` 定义 + 13 条主定理；经 `清单:401-408`）
  - `L5:1833-1884`（`RuleDrivesEndToEnd` / `RuleEntersWorldModel` 的模块自述与定义清单）
  - `L12:1670-1688`（`FcaRuleEntersWorldModel`：`dgToRichLaw` + `richLaw_isDirac_iff_exists_detFun`）
  - `清单:581`（`RuleDrivesEndToEnd,ruleWorldModel_endToEnd_fixed_iff`）
  - `L5:229-260`（`AlphaStatistical`：α 的统计版，`statAlpha_isPoint_iff`）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：链上有一处**被明写的类型错误级障碍**：`LawRuleCondMul` 的结论是「`CondMul` 能用 `LawRule` 表达，但代价是把联合律整体塞进状态，`IsPoint`/`generalize`/`refine`/`compose` 全部退化——那不是忠实表达，是重命名」（`L9:478-482`）。

---

## 候选 10 · 图 ⟹ 概率桥 + 后门/前门调整（识别式预测）

- **一句话**：预测不是从数据拟合出来的，而是**从图推出来的**：先证「图上的 d-分离 ⟹ 概率上的条件独立」，再用后门/前门的**调整公式**把 `P(y|do(x))` 算成可观测量的加权和。
- **输入**：DAG `G`（+ 因子分解 `p x = ∏_v f_v x`，或 SCM 的 `(pU, sg)`）。
- **输出**：干预律 `P(y|do(x))`（用 `adjustLaw`/`frontdoorFormula` 从观测量算出），或「不可识别」的判定（调整集不存在 / positivity 失效）。
- **部件链路**：
  1. 图侧：`dSep`（路径层→方向层→后代层，逐层形式化）
  2. 桥：`Factorizes + dSep ⟹ CondIndep`（`BridgeDSepGeneral` 的一般整合版；另有 20+ 种候选策略，见「备注」）
  3. 识别：`BackdoorConditions`（`BackdoorSep ∧ NoDescendant ∧ NoOutcome ∧ ObservableOnly`）⟹ `adjustLaw(W) = doLaw`
  4. 前门：`FrontdoorConditions`（(i) 截断所有有向路径 (ii) 无未阻断后门 (iii) 覆盖）⟹ `frontdoorFormula = doLaw`（**需 positivity**，无 positivity 有反例）
  5. 接线：`WiringBackdoor` / `WiringFrontdoor` 把上述三条线接到 `WorldModel` 的干预能力上（`wmAdjustEst_eq_doLaw`）
- **与其它候选的关键区别**：① 唯一一条**输出是「反事实量」而输入只有「图」**的候选（其余候选都要数据或参数）；② 唯一一条把「**不可识别**」也当成合法输出的候选（反例、降级声明是它的一等公民）；③ 与候选 3/4 正交：管线负责「用残差学参数」，桥负责「把干预量算出来」。
- **证据**：
  - `L7:9-49`（`BackdoorGenuine`：`backdoorConditions_iff` / `backdoorSep_iff`，含第 297 轮降级声明）
  - `L7:3266-3295`（`WiringBackdoor`：后门三条线 ⟹ `WorldModel`，`wmAdjustEst_eq_doLaw`）
  - `L12:433-444`（`BridgeDSepGeneral`：`split_of_dSep` + `condIndep_of_factorizes_general` 串成一条）
  - `L12:196-206`（`FrontdoorCriterion`：Pearl Thm 3.3.4 三条件；`exists_formula_failure` 反例）
  - `清单:41-47`、`清单:9-49`（`BackdoorGenuine` / `BackdoorWithM`）
- **成熟度**：**完整定义+代码**（但见备注）。
- **备注（冲突）**：桥本身**未闭合**且是本库最大的失败记录区——`L7:2996-3003` 逐字写「前 19 种策略的失败模式被反复登记」「`dSep ⟹ CondMul` 这条桥在库里**没有一条定理真正用它做前提**」；`L12` 里同一条桥有 20+ 个视角文件（`View2/3/6/9/10/11/14/15/16/17/18/19/20/Strategy9/11/12/13`），且多份带「降级声明」。

---

## 候选 11 · 分档塔（预测档 / 干预档 / 反事实档，各用不同桥）

- **一句话**：不追求「一个桥打穿三层」，而是承认**只有分档**：预测档读 `P(V)`、干预档读干预分布族、反事实档读逐个体响应；三档成一条**链**，粗档能单值 ⟹ 细档也能单值（其逆不成立）。
- **输入**：SCM 集 + 图 + 档位 `τ ∈ {predict, intervene, counterfactual}`。
- **输出**：该档的读出是否**单值**（可区分）/ 是否**塌缩**；跨档的免费结论（粗档单值 ⟹ 细档单值）。
- **部件链路**：
  1. `Tier`（三档）+ `Tier.le`（全序，`tier_chain`）
  2. `Bridge {induce : SCM → Graph, bridge : Tier → Graph → Set SCM, sound}`（**按档索引的集合值逆映射**）
  3. `Obs {Val : Tier → Type, obs : ∀ τ, SCM → Val τ}`（**按档索引的读出泛函**）
  4. 塔假设两侧：`IsTowerB`（细档纤维 ⊆ 粗档纤维）/ `IsTowerO`（细档泛函 = 粗档泛函 ∘ 遗忘）
  5. `DiscrimOn` / `CollapseOn`（该档在 `F` 上可分/全同）
  6. 核心单向定理：粗档单值 ⟹ 细档单值
- **与其它候选的关键区别**：① 唯一一条**显式放弃「统一」**的候选（承认三档各用不同桥）；② 唯一一条把「**输出精度**」当成档位属性的候选（点值/区间/集合）；③ 它是候选 10 的**上位设计**：候选 10 说「桥怎么搭」，本候选说「桥有几种、档与档之间什么关系」。
- **证据**：
  - `Fate/TieredScheme.lean:12-31`（三档表 + 「塔给出单向免费结论」+ 「其逆不成立」）
  - `Fate/TieredScheme.lean:43-57`（`Tier` / `Tier.le` / `tier_chain`）
  - `Fate/TieredScheme.lean:69-83`（`Bridge` / `Obs`）、`:88-98`（`IsTowerB` / `Refines` / `IsTowerO`）、`:108-113`（`DiscrimOn` / `CollapseOn`）
  - `L7:92-118`（模块自述）、`映射:723`（`TieredScheme,L7,8,9`）
- **成熟度**：**只有骨架**（6 条主定理；`IsTowerB`/`IsTowerO` 是**假设**不是定理；模块自述自承「塔也不免费提供塔顶」）。
- **备注（冲突）**：三档的「读出」在代码里是**类型参数**（`Val : Tier → Type`），**没有任何一个具体实例**把三档的 `Val` 填成 `P(V)`/干预分布族/响应函数——即分档方案**从未被实例化**。

---

## 候选 12 · 反事实三步（溯因 → 干预 → 预测）/ 不可观测时降为区间

- **一句话**：反事实是**三步算子**：先用观测证据 `E=e` 更新外生律（溯因 `P(U|e)`）、再替换 `X` 的方程（干预）、再用后验算 `Y` 的律（预测）；当外生 `u` 完全不可观测时，输出不是点值而是**最紧的区间**。
- **输入**：SCM + 观测证据 `E = e` + 假设的干预值 `x'`（+ 是否可溯因）。
- **输出**：反事实点值 `cfWithAbduction`；或区间 `[cfLower, cfUpper]`（`SoundInterval` + `open_zero_one_is_tightest` 证明该区间最紧）。
- **部件链路**：
  1. 溯因：`postZ`（后验 `P(U|e)`）/ `obsEventMass`
  2. 干预：替换 `X` 方程为常数
  3. 预测：`cfWithAbduction`（带溯因）vs `cfNoAbduction`（不带）
  4. 退化判据：`cf_eq_doLaw_iff`（**何时反事实退化为干预**）；`CfNecessity` 给出「溯因是否必要」的机理分析
  5. 部分识别：`cfIdentSet` / `cfLower` / `cfUpper`；`PointIdent ↔ lower = upper`
  6. 视角一支持反事实时输出**集合值**：`cfSetObs` / `PointValuedCF ↔ obs 常值`
- **与其它候选的关键区别**：① 唯一一条**输入含「证据」而非常规数据**的候选（贝叶斯式更新外生律）；② 唯一一条把「**识别失败**」形式化成区间且证明区间**最紧**的候选；③ 与候选 10 分工：候选 10 给「群体层的干预律」，本候选给「个体层的反事实」。
- **证据**：
  - `L7:2767-2791`（`T43Abduction`：Pearl §7.1.2 三步逐字 + `cfWithAbduction` / `cfNoAbduction`）
  - `L7:1049-1076`（`CfPartialIdent`：O3 三档 + `cfLower`/`cfUpper`/`PointIdent`）
  - `L7:1095-1106`（`CfPartialIdentConsumer`：`SoundInterval` + `open_zero_one_is_tightest`）
  - `L7:3218-3240`（`ViewOneCounterfactual`：「能，但输出是集合值/区间，非点值」）
  - `清单:147-152`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`T43Abduction` 的主定理是**否定式**（`M_no_diff` / `M₂_no_diff`：溯因在本载体上**不改变**结果），即「三步算子」在本库里**更多被用来证「哪一步可以省掉」**，而不是「三步缺一不可」。

---

## 候选 13 · θ 学习收敛（参数是「点」或「函数」）

- **一句话**：学习 = 参数 `θ` 沿 `θ_{n+1} = θ_n + η(θ* − θ_n)` 收敛到真值 `θ*`；`Θ.Carrier` 既可以是**点**（`ℝ^d`）也可以是**函数**（逐点 Dirac 学习），两者表达力不同。
- **输入**：观测 `y = h x + η`、参数空间 `Θ`（点或函数）、步长 `η`、初值 `θ₀`。
- **输出**：`θ_n → θ*`（唯一、且 `θ*≠0`），并使 `sim` 的轨迹随之收敛；函数档是「在 `x` 处收敛、其他点不动」。
- **部件链路**：
  1. `ParamSCM`：给 SCM 加参数空间 `Th`，使 `Θ` 不再退化（原 `scmThetaSpace` 是单点 `PUnit`）
  2. `ThetaMatters`（Z2）：先证 `θ` **真的有作用**（`step_discarding_theta_exists` / `theta_blind_mechanism_exists` 是反例）
  3. `ThetaConvergence`（Z3）：`thetaN` 迭代 ⟹ `linWorld_tendsto_thetaStar`（学到真值，不是学到零）
  4. `ThetaLearningParam`：把「θ 收敛」与「sim 依赖 θ」串成一条（`sim_tendsto_of_theta_learning`）
  5. `ThetaExpressiveness`：`Θ.Carrier` 是点 vs 是函数（`point_expressible_imp_fun_expressible`，逆不成立）
  6. `LearnFunction` / `LearnFunctionUnified`：函数档的收敛（`tendsto_stepFunN_apply` / `tendsto_to_goal`）
- **与其它候选的关键区别**：① 唯一一条**输出就是「参数值」**的候选；② 唯一一条把「参数空间的**基数**」当作设计变量的候选（点 vs 函数）；③ 与候选 8 相反（候选 8 排除候选，本候选逼近真值）。
- **证据**：
  - `L2:9-32`（`ParamSCM`：「给 SCM 加上参数空间 `Th`，使 `Θ` 不再退化」）
  - `L2:83-108`（`ThetaConvergence`：Z3「真正收敛到真值 θ*」；四条主定理）
  - `L2:141-163`（`ThetaLearningParam`：五个 `thetaN_converges_*` / `sim_tendsto_*`）
  - `L2:111-137`（`ThetaExpressiveness`：点 vs 函数）
  - `L6:239-272`（`LearnFunction`：GG2「学习一个函数（不是学习一个参数）」）
  - `映射:476`、`映射:716-719`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`LearnFunction` 明确登记 `not_converges_globally`（**不全局收敛**）——函数档只在被观测的那点收敛，其余点保持初值，所以「函数档更强」是有代价的。

---

## 候选 14 · 观测反推潜变量的三档（bounded / posterior / quotient）

- **一句话**：从观测 `y` 反推潜变量 `w` 有三档，且这三档是**同一个结构的三次特化**：强档给点估计（带误差界）、中档给后验、弱档只能给等价类（商）。
- **输入**：观测 `y : Y`、映射 `h : W → Y`、误差界 `δ`。
- **输出**：`w` 的点估计（`estOf`，满足 `est_within_bound`）/ 后验 `post` / 等价类 `classOf`（商 `I.quo`）。
- **部件链路**：
  1. `InversionTier`（三档：`bounded` / `posterior` / `quotient`）
  2. `Inversion {h : W → Y}` → `ker` / `quo` / `classOf`（商档）
  3. `PosteriorData.post`（后验档）
  4. `BoundedData.estOf`（有界档，`est_within_bound`）
  5. 三档关系：`tier_output_shape_bounded_ne_quotient`（**输出形状不同，不可互换**）、`strong_implies_quotient`
  6. 消费：`tierToScheme`（把三档接到候选 11 的分档塔上）
- **与其它候选的关键区别**：① 唯一一条**输出是「不确定性的形状」**（点/后验/等价类）的候选；② 它是 A14（观测状态）与 O3（外生不可观测）两处三档的**统一抽象**（材料明言二者同构）；③ 与候选 12 的「区间」区别：这里是**语义层的三档**，不是数值区间。
- **证据**：
  - `L1:35-72`（`ObservationUnified`：A14/O3 三档对照表 + `InversionTier`/`Inversion`/`PosteriorData`/`BoundedData`）
  - `Fate/ObservationUnified.lean:105`（`InversionTier`）、`:119`（`Inversion`）、`:222`（`PosteriorData`）、`:293-312`（`BoundedData` / `estOf`）
  - `L1:221-243`（`ObservationUnifiedConsumer`：`tierToScheme` 把三档接分档塔）
  - `映射:466`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：三档之间**没有**「强档包含弱档」的定理（只有 `strong_implies_quotient` 一个方向），而 `tier_output_shape_bounded_ne_quotient` 证明形状不同 ⟹ 三档**不能互相替代**。

---

## 候选 15 · 误差判据系统（拟合边界 + σ 四破法 + 双轨误差图）

- **一句话**：系统自带一套「**什么时候算预测得够好**」的判据：误差必须落在 `[σ/2, 2σ]`（刚好拟合与过拟合的边界）；σ 本身用四条互不替代的路径估；误差**同时报端到端与逐层两条，且不相加**。
- **输入**：误差剖面 `err(γ)`（随分辨率 `γ` 变化）、噪声尺度 `σ`、样本数 `n`、数据 `P`。
- **输出**：合格判据 `Canonical ε σ`、拟合边界 `γ*`（`IsFitBoundary` / `HasFitBoundary`）、误差带、以及一张**带类型的误差图谱**（`E2E` + 逐层 `LayerErr`，各自 `OK` 判定）。
- **部件链路**：
  1. `ErrProfile` / `IsFitBoundary(W,σ,γ)`：误差**恰好等于** σ 的那个 `γ`
  2. `HasFitBoundary`：存在 `γ` 使 `err γ = σ` **且** σ 是下界
  3. σ 的四条破法：`SigmaFromDomain`（领域参数传入）/ `SigmaFromAIC`（AIC/BIC 拐点）/ `SigmaFromInfoGain`（信息增益判据）/ `SigmaGammaFromData`（σ↔γ 循环破解）
  4. `SigmaUnified`：四路汇合（`capstone_sigmaFrom*` 四条）
  5. `ErrorCriterion.Canonical ε σ := σ/2 ≤ ε ∧ ε ≤ 2σ`；`ErrorCriterionUnified` 证明**四处判据等价**
  6. `ErrorGraph`：`E2E`（端到端）+ `∀ L, LayerOK`（逐层），`OK ↔ gateOK ∧ ∀ L, LayerOK`（**不相加**）
  7. `ErrorMagnitude`：三分量（方差/范数/损失）的可比语义
- **与其它候选的关键区别**：① 唯一一条**输出是「判定」而不是预测值**的候选；② 唯一一条把「**噪声尺度 σ 从哪来**」当作独立子系统的候选（四条破法 + 汇合层）；③ 唯一一条明确「**端到端与逐层双轨、不相加**」的候选（作者裁决 E）。
- **证据**：
  - `L8:9-41`（`ErrorGraph`：作者裁决 E「误差量纲不需要统一…两者都报、不相加」+ 四层结构）
  - `L8:123-167`（`FitBoundary`：`IsFitBoundary`/`HasFitBoundary`/`IsFitBoundary_scale`/`existsUnique_isFitBoundary_of_strictConvexOn`）
  - `L8:915-943`（`ErrorCriterionUnified`：「裁决 K 误差判据的**唯一权威口径**」，四处判据对照）
  - `L8:85-120`（`EndToEndError`：`DualReport` / `same_layer_diff_e2e`）
  - `映射:595-600`（σ 四模块 + `SigmaUnified`）
  - `清单:1038-1055`（`ErrorMagnitude` 的 9 条主定理）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：σ↔γ 是**循环依赖**（定边界要 σ、估 σ 要先有分辨率），四破法各自只解一半；`SupportBound` 还给出负面结论「`γ` **没有**数值上界」（`no_numeric_upper_bound_on_gamma`）。

---

## 候选 16 · 评估/审计子系统（死前提审计 + 三套科学哲学评价 + 最优性模式）

- **一句话**：系统里有一层专门「**审自己**」：先查一条定理的前件是不是恒真（死前提）、再用 Popper/Occam/Lakatos 三套（外加 `ruleSpec` 一套）科学哲学判据给规则排序、再用「界紧唯一性」模式统一各种最优性。
- **输入**：一条定理/一条规则对 `(r1,r2)`/一组维度 `Dimensions`。
- **输出**：`AuditVerdict`（有内容 / 同义反复 / 死前提）、`Better r1 r2` 的偏序、以及「该最优值唯一且界紧」的判定。
- **部件链路**：
  1. `TautologicallyTrue` / `DeadPremise` / `HasContent` / `AuditVerdict`
  2. 元定理：`imp_iff_right_of_tautologicallyTrue`（前件恒真 ⟹ `P→Q` 等价于 `Q`，即该定理**没有内容**）
  3. `EvaluationSystems.Dimensions`（8 个实值维度）+ 四套 `EvaluationSystem`：`popperSystem` / `occamSystem` / `lakatosSystem` / `ruleSpecSystem`
  4. `RuleEval.Better`（三套各自的 `*_better_iff`）与 `MetaBetter`
  5. `ScoreK.bandLoss`（把「损失最小化」与「裁决 K 的带判据」统一成一个打分）
  6. `OptimalityPattern`：把「界紧 + 唯一」抽象成模式，`GaussMarkov` 与 `OptimalEta` 都是它的实例
  7. `Audit10Factorizes` / `Audit10Factorizes`（独立复核某定义体是否真的表达了因子分解）
- **与其它候选的关键区别**：① 唯一一条**输入是「命题」而不是数据**的候选；② 唯一一条把「**同义反复**」做成可判定谓词的候选（审计器本身是形式化的）；③ 与候选 15 分工：候选 15 判「误差够不够小」，本候选判「定理有没有内容」。
- **证据**：
  - `Fate/DeadPremiseAudit.lean:19-30`（「把一次性审计做成**可复用审计器**」四项目标）
  - `Fate/DeadPremiseAudit.lean:38-49`（`TautologicallyTrue P := P` 的设计说明与两个层次的区分）
  - `L11:9-39`（`EvaluationSystems`：`Dimensions` / `EvaluationSystem` / 四套系统 / 5 条主定理）
  - `L11:187-206`（`ScoreK`：判准 1 损失最小化 ⊕ 判准 2 裁决 K，`bandLoss`）
  - `L11:78-109`（`OptimalityPattern`：界紧唯一性模式）
  - `清单:277-280`（`ruleSpecSystem_better_iff` / `popperBetter_iff` / `occamBetter_iff` / `lakatosBetter_iff`）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`EvaluationSystems` 的判据里 `Dimensions` 是**纯参数**（8 个实值由外部填），所以「哪套科学哲学对」在代码里**不可判**，只能判「在同一组维度下哪套判据给出什么序」。

---

## 候选 17 · 裁决 K + 两版本并存（信息完整度 ⟹ 唯一最优；或承认不唯一）

- **一句话**：系统的「能不能给出唯一答案」被归结为**信息完整度**：数学侧可获完整信息，故最小点/边界唯一；而在信息不完整或算子非单射时，系统**主动改为「两版本并存」**并给出不唯一的反例。
- **输入**：误差函数 `f : ℝ → ℝ`（或误差剖面 `W.err`）/ 算子 `A`、`φ`、观测 `x'`。
- **输出**：`∃! γ, IsMinOn f univ γ`（唯一最优）与 `∃! γ, IsFitBoundary W (W.err γ) γ`；或版本 2 的「唯一解 + 收敛到 `φ x'`」；或**不唯一**的反例。
- **部件链路**：
  1. `InfoComplete f`（信息完整）⟹ `exists_min_of_infoComplete` / `minUnique_of_infoComplete`
  2. 反方向：`not_infoComplete_of_notUniqueMin`（不唯一 ⟹ 信息不完整）、`infoComplete_excludes_notUnique`
  3. 边界版：`fitBoundary_existsUnique_of_infoComplete`
  4. 反例层：`hingeErr` 有两个极小 ⟹ `not_infoComplete_hingeErr`（**信息完整度是可反驳的**）
  5. 两版本：版本 1（`Corrects` ⟹ 误差 `|1-η|^n` 收敛，**不需 φ 单射**）/ 版本 2（`Corrects + φ` 单射 ⟹ 收敛到**唯一** `θ*`）
  6. 唯一性的充要条件：`T1MultiDim`（`unique_iff_span_top` 等）
- **与其它候选的关键区别**：① 唯一一条**主句是「唯一性」**的候选（其余候选谈「有没有」「准不准」，本候选谈「**是不是只有一个**」）；② 唯一一条把「**承认不唯一**」做成正式版本（版本 2 与反例并存）的候选；③ 它是候选 15 的**元层**：候选 15 用 σ 定边界，本候选回答「边界为什么唯一」。
- **证据**：
  - `L10:85-113`（`AdjudicationKUnified`：裁决 K 原文「数学可以获得完整信息」+ 13 条主定理清单）
  - `L10:234-269`（`TwoVersions`：版本 2 的 12 条主定理；`version2_main` / `counter_not_unique`）
  - `清单:5-12`（`exists_min_of_infoComplete` … `notUniqueMin_hingeErr`）
  - `路线图:1486-1533`（L10 层 8 条「被审计提过」的主定理全文）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`InfoComplete` 的定义在代码里是**对 `f` 的一个谓词**，其「现实侧不完整」这一半**不在 Lean 里**（裁决 K 只是把它写成注释与命题的对偶），所以「两版本并存」更像是**工程妥协的形式化**，不是理论结论。

---

## 候选 18 · 「四 + 甲」多腿组装（联合观测泛函 ⟹ 整体可识别）

- **一句话**：整体可识别性不是靠一条大定理，而是**把多条「腿」（不同观测泛函）拼成一个联合泛函**：`obsJoint s = (obsDir s, obsFun s)`，其核 = 各腿核之交；只要两腿「互不遮蔽」，联合忠实 ⟺ 两腿都忠实。
- **输入**：方向层观测 `obsDir : SCM → Dir`（「四」）+ 函数层观测 `obsFun : SCM → Fun`（「甲」）。
- **输出**：整体可识别（`obsJoint` 单射 / 在纤维上单值）；以及**归约到的显式剩余前件** `FunSingleOnFiber`。
- **部件链路**：
  1. `obsJoint`（按对拼接，联合观测泛函）
  2. `ker(obsJoint) = ker(obsDir) ∩ ker(obsFun)`（A1）
  3. `NonMasking`（互不遮蔽）⟹ 「两腿都忠实 ⟺ 联合忠实」（A2），且 `nonmasking_necessary_witness` 证明该前件**不可省**
  4. `FunSingleOnFiber`（甲的观测在四的方向像纤维上单值）⟹ 联合在纤维上单值（A3，且逆命题成立）
  5. `joint_injective_iff`（A4：联合单射 ⟺ 无「两腿都读不出差别」的机制对）
  6. 实例化：`AssemblyInstance`（线性 SEM 上的非空实例）
- **与其它候选的关键区别**：① 唯一一条**以「组合」为主句**的候选（其它候选是链或循环，本候选是**拼装**）；② 唯一一条**主动把未证内容隔离成一个具名前件**的候选（材料原话：「把一个大而未形的缺口换成一个小的、具名可攻的缺口」）；③ 输出不是预测值而是「**识别性**」。
- **证据**：
  - `Fate/Assembly.lean:9-56`（「四+甲」的数学内容：方向层/函数层/组装 = 联合泛函；A1–A4 四条）
  - `Fate/Assembly.lean:67-76`（诚实边界：`FunSingleOnFiber` 未被从主定理推出，只隔离为显式前件）
  - `Fate/Assembly.lean:94-95`（`obsJoint` 实体）
  - `L1:171-194`（模块自述 + 3 条主定理）
  - `清单:31-33`
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：`AssemblyMeta` 另给一条「**装配无收益**」的对偶结论（`assembly_no_gain` 是定义展开），故「多腿拼装一定更强」在本材料里**不成立**——只有「两腿互不遮蔽」时才是等价的。

---

## 候选 19 · 世界模型主定理（capstone 单点收口：一条定理装配全部）

- **一句话**：整个系统被压缩成**一条合取式主定理**：给定一个 `ClosedLoopWorld` 与数据，一次性得到「收敛到 `θ*` + 噪声稳态界 + σ 可接受 + 参数可识别 + 因果接口一致 + 误差带」。
- **输入**：`W : ClosedLoopWorld E F`、`θ*`、`x ≠ 0`、两个互异参数 `θ₁ ≠ θ₂`、概率测度 `P`、样本数 `n > 0`、算子 `A`、`φ`、Lipschitz 常数 `L`。
- **输出**：六件事的合取（收敛 + 稳态界 + σ 判据 + 识别 + 因果接口 + 误差带），以及「前件可满足」的见证（`capstone_premises_satisfiable`）。
- **部件链路**：
  1. 上游 8 个模块被 `import` 并在**证明体内真实调用**（非仅 `#check`）
  2. `ClosedLoopWorld`（世界模型的闭环实例）
  3. `worldModel_capstone`：24 条细依赖串成的合取
  4. `WorldModelMainTheorem.worldModel_main_theorem`：进一步收口版本
  5. `capstone_premises_satisfiable` / `main_premises_satisfiable`：证明前件非空
- **与其它候选的关键区别**：① 唯一一条**「系统 = 一条定理」**的候选（其余候选是部件链）；② 唯一一条把「**装配本身**」当作交付物的候选（材料的原话是「全库唯一一条真正的世界模型装配定理」）；③ 它是候选 3/4 的**收口形态**：管线给出环节，capstone 给出合取。
- **证据**：
  - `路线图:1330-1336`（`worldModel_capstone`：24 条细依赖，`WorldModelCapstone` L742）
  - `L9:978-993`（`WorldModelMainTheorem`：「世界模型的最终交付物 / 真正的收口点」；`worldModel_main_theorem` / `main_premises_satisfiable`）
  - `L9:164-183`（`WorldModelCapstone`：51 条定理、26 条主定理特征）
  - `清单:1294-1341`（`c_pos_iff` … `capstone_premises_satisfiable`）
- **成熟度**：**完整定义+代码**。
- **备注（冲突）**：材料的审计 R96 判定它此前**扇入 = 0**（「只被 `Fate.lean` 点名，没有任何别的模块 import 并使用其定理」），故「一条定理装配全部」的**装配性**本身是被事后补的消费者（`WorldModelCapstoneConsumer` / `WorldModelSynthesis`）追认的。

---

## 候选 20 · 十三层静态栈（模块 → 理论层的元结构）

- **一句话**：代码自己把系统切成**13 个理论层**（L1 对象与轨迹 … L13 未归类），每层有固定的主定理配额；这是**唯一的全局架构陈述**，也是「世界模型/裁决/评估三层只存在于代码」的证据。
- **输入**：无（这是元结构，不是数据流）。
- **输出**：每个模块的层归属 + 该层的主定理数 / 零细依赖数 / 被审计提过数。
- **部件链路**（层栈，按层号）：
  1. `L1-对象与轨迹`（8 主定理）：`Basic`（`StateSpace`/`Tmax`/`ThetaSpace`/`InputSpace`/`ActionSpace`/`NoiseSpace`）、`Assembly`、`InstanceChain`
  2. `L2-命与运`（10）：`ParamSCM`、`ThetaConvergence`、`ThetaMatters`、`ThetaExpressiveness`
  3. `L3-因果结构`（50）：`DAGBridge`、`PearlGlobalMarkov`、`SCMSemantics`、`SCMGraph`、`SCMWorldModel`
  4. `L4-轨迹生成`（4）：`Stage1A`
  5. `L5-规则层与FCA`（131）：`Frame`、`FCA`、`Alpha*`、`Implication`、`Completeness`、`RuleSyntax*`
  6. `L6-规则学习/估计`（7）：`FinMarkov`、`FinJoint`、`StatAlpha`、`LearnFunction`
  7. `L7-预测/干预/反事实`（134）：`EndToEnd*`、`Intervention*`、`Pipeline*`、`Backdoor*`、`Frontdoor*`、`T43/T44`
  8. `L8-误差/假设`（101）：`Error*`、`FitBoundary*`、`Sigma*`、`Residual*`、`ChainErrorBudget*`
  9. `L9-世界模型`（85）：`WorldModel`、`WorldScenario`、`WorldModel*`、`LawRule*`、`ClosedLoop*`
  10. `L10-裁决机制`（22）：`Adjudication*`、`TwoVersions`、`MultiObject`、`LipschitzFromFinite`
  11. `L11-评估系统`（16）：`EvaluationSystems`、`DeadPremiseAudit`、`OptimalityPattern`、`ScoreK`
  12. `L12-桥`（122）：`Bridge*`、`View*`、`Strategy*`、`Nary*`、`CondIndep*`
  13. `L13-未归类`（147）：147 条主定理无处安放（含 `OptimalEta`、`GaussMarkov*`、`CellDiameter`、`Scenario*`）
- **与其它候选的关键区别**：① 唯一一条**不描述数据流、只描述归属**的候选；② 它暴露了一个结构性事实：**层的顺序与数据流的顺序不一致**（`L12-桥` 在 `L9-世界模型` 之后编号，但桥是因果→概率的前置；`L13` 有 147 条主定理**无层可归**）；③ 它是「世界模型/评估/裁决三层在净版正文里完全没有」这一事实的**唯一来源**。
- **证据**：
  - `路线图:18-32`（13 层总览表：主定理数 / 有细依赖 / 零细依赖 / 被审计提过）
  - `路线图:3`（来源：802 模块静态解析，833 条主定理 + 2,136 条定理级依赖）
  - `映射:1-803`（802 行模块→层映射，含定理数/定义数/字节数/模块文档首行）
  - `L9:1-3`（L9 层 = 42 个模块）、`L10:1-3`（11 模块）、`L11:1-3`（9 模块）
- **成熟度**：**只有代码**（层号来自扫描产物，不是理论文档的章节结构；净版正文 8 章骨架与此 13 层**没有映射表**）。
- **备注（冲突）**：`L13-未归类` 147 条主定理（占 833 的 17.6%）说明**分层本身是失败的**——最大的一类就是「归不进去」。

---

## 附：本视角看到的「结构性事实」清单（不构成候选，供去重时参考）

1. **「层」做全了，「链」做断了**：`Fate.lean` 1202 行 import、802 模块，但 `路线图` 统计的 833 条主定理里 **223 条零细依赖**（证明体里不调用任何本库定理）——即近 27% 的主定理是**孤点**。
2. **三层只活在代码里**：L9 世界模型（42 模块）、L10 裁决（11）、L11 评估（9）在净版正文**无对应章节**（净版「世界模型」出现 0 次）；而净版 v1.0 有 154 个 `[命题/定理]` 编号、v2.0 有 0 个。
3. **同一件事的多套口径在代码里并存**：世界模型有 `WorldModel`（7 字段）、`WorldModelCompleteV2`（交器重做版）、`WorldModelCompleteV2W`（弱化版）、`ClosedLoopWorld`（capstone 版）**四个互不相同的结构**，且 `WorldModelCompleteV2.lean` 自己登记「全库唯一的 `Fate.WorldModel` 类型只有 7 个字段」（`L9:194-196`）。
4. **「桥」是全库最大失败区**：L12 层 138 个模块、122 条主定理，同一条 `dSep ⟹ CondIndep` 有 **20+ 个视角**（View2/3/6/9/10/11/14/15/16/17/18/19/20、Strategy9/11/12/13…），其中多份带「降级声明」「机检反例」「本文件没推进缺口」。
5. **「已证」栏为空的代码对应物**：`VerifyFalseClaim`、`GapFalse`、`GapIsFalse`、`SinkPeelFinalVerdict`、`TowerAudit`（`mass` 塔性质被证伪）、`LMGcFinalVerdict`（`FactorizesC ⟹ LMGc` 被机检证伪）——**负面结论是这一层最扎实的产出**。
