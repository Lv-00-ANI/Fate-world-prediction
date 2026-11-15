# ⚠⚠⚠ 第 495 轮修正标注（**读本文件前必读**）

## 一件事：本文件的「✅ 已实现」判定**偏高**

**审计 R480（第 483 轮）与主控（第 494 轮）分别独立复核后一致认为：**
**本文件判为「✅ 已实现」的条目里，有 2 条应为「🟡 部分」。**

**详细裁决见**：`_audit/H3-开放问题判定冲突裁决.md`（第 494 轮，主控读源码逐条仲裁）

## 三处冲突的最终裁决

| # | 开放问题 | 本文件（H1）| 审计 R480 | **最终裁决（H3）** | 源码依据 |
|---|---|---|---|---|---|
| **2.1** | `u_t`/`ε_t` 区分 | ✅ | 🟡 | **🟡** | `Step F := X → U → Ν → Θ → Act → X` 是**任意函数类型**，可取 `fun _ _ _ _ _ => x₀` **忽略全部** ⟹ **类型分开 ≠ 语义区分** |
| **5.2** | 结构性指标 | ✅ | 🟡/❌ | **🟡** | `Identifiable`（`SCMIdentifiability:217`）是**`ParamSCM.Th` 的可识别性**，**不是 `Rule` 的质量度量**；`Recoverab` **零命中** |
| **5.5** | FCA 与 α | ✅ | ❌ | **🟡** | `polarUp_eq`（`AlphaFCAConstruction:129`）证明是 `ext` + `rw [mem_polarUp_iff]` + 双向 `exact` ⟹ **定义展开**，**不是「`(·)'` 到 `α` 的映射」** |

## 修正后的最终统计（**以此为准，覆盖本文件 §二**）

| 判定 | 数量 | 编号 |
|---|---|---|
| ✅ **已实现/已裁决** | **2** | **5.1、5.3** |
| 🟡 **部分实现** | **11** | 1.1、1.2、1.3、1.4、**2.1**、2.2、**5.2**、5.4、**5.5**、5.6、5.7 |
| ❌ **未实现** | **2** | **1.5、6.10** |
| ⚠ **净版问题** | **2** | 2.3（过时，Q-1 推翻）、2.4（分类，非过时） |
| **合计** | **17** | |

**⟹ 所以「已实现」是 2/17 = 12%**（**不是本文件 §二的「3 个」**）。

## 本文件仍然有价值的部分

**⟹ 本文件的行号证据（`文件:行号`）是准确的** —— **问题只在「这是否构成净版要的那个东西」这个判断标准**。

**⟹ 正如 `H3` §五 所说**：「判定标准是『净版原文要什么 vs Lean 给了什么』——这是**语义匹配**，不是**形式匹配**」。

**⟹ 本文件用的是形式匹配（`grep` 看到名字就判），所以偏高。**

---

**（以下为本文件原文，保留不改）**

---
# H1 净版 17 个开放问题 · Lean 实现核查（第 474 轮任务 / 第 478 轮 H1 代理实查修订版）

> **文档类型**：审计报告（理论文档 ↔ Lean 实现的事实核查）。
> **读者**：项目维护者（主控）。
> **本轮修订说明（必读）**：本文件原名「第 474 轮主控快速版」，主控自述「用 `grep` 快速筛，**未逐个通读候选模块**」，
> 并已记录 3 处修正（第 476 轮修 6.10、第 477 轮修 2.2 与 5.5）。
> **第 478 轮由 H1 代理对每一条逐一遍读源码后重写本文第二、三节**，汇总表保留「历次判定的演进」以免历史丢失。
> 凡与旧版判定不同者，在表中以 **⟳** 标出并附新旧理由。
>
> **纪律**：只读。**未对 `/root/fate-dev/Fate/` 下任何文件做写/删/移**（只 `grep`/`sed`/`head`/`python3 -c` 读）。
> 未改任何既有 `.md`，未碰任何 `.lean`。
> **每条判定附实测证据**（命令输出 / 文件:行号 / 定理名）。**区分「真的实现了」与「名字像但语义不同」**，后者明确点出。
> 凡未核实者标「未核实」。

---

## 0. 核查环境与基线

| 项 | 实测值 | 命令 |
|---|---|---|
| 服务器 | `ct.hylab.im`（`node C:\Users\xingg\Desktop\服务器\.sshnode\run.js`） | — |
| 仓库 | `/root/fate-dev` | — |
| **HEAD（核查期间推进过）** | 起始 `f3b9083`（`feat: ComposeUnified 入链`）→ **核查进行中推进到 `6b6d0f4`（`feat: ActInputDecomp 入链（11 定理）—— 开放问题 2.2 的完整回答`）** | `git log --oneline -3` |
| `Fate/` 下 `.lean` 文件数（含子目录） | **677**（`Fate/*.lean` 顶层 **620**） | `python3 -c` `os.walk` / `os.listdir` |
| 链上模块数 | **604** | `grep -c -e 'import Fate\.' Fate.lean` |
| 定理 + 引理总数（`Fate/*.lean`，顶层 `^theorem`/`^lemma`） | **7689** | `python3` 逐文件正则统计 |
| **构建** | **成功**：`Build completed successfully (9275 jobs).` EXIT=0 | `export PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin; lake build Fate` |

> ⚠ **HEAD 在核查期间前进了**（`f3b9083` → `6b6d0f4`）。C6（第 376 轮）基线 `1f30ffa` / 578 模块；E1（第 422 轮）591；本轮 604。
> **本报告所有结论均基于卷上实际文件内容（逐条 `sed`/`grep` 读过），不依赖任何旧快照的扇入数字。**

**⚠ 工具限制（影响取证方式，必须先声明）**：SSH 包装层 `run.js` 用 `process.argv.join(' ')` 拼命令，
导致 `$` 在远端被 shell 展开、双引号被剥离。因此：
- 本报告**未使用**任何 `$(...)`、`for` 循环、带 `$` 或含双引号的模式；
- 取证全部走 `grep -n -e PATTERN`、`sed -n 'a,bp'`、`head`、`python3 -c '...chr(n)...'`（用 `chr()` 构造引号与正则锚点）；
- **一次错误取证已作废**：我曾执行 `grep -rl "import Fate.WorldModel$"`，`$` 被吞后退化为无锚点匹配，**返回了全部文件**。
  **该输出已作废，未进入任何结论**。另 `grep -rl "import Fate.WorldModel"` 也因 `Fate.WorldModel: 没有那个文件或目录` 的 stderr 混入而不可信。

---

## 一、汇总表

| # | 开放问题 | 净版说法 | Lean 现状（第 478 轮实查） | 判定 |
|---|---|---|---|---|
| **1.1** | 路径空间的测度 | 「从未给出该路径空间与其上的测度」 | `TrajGenStochastic.trajLaw`（`:201`）已构造**有限视窗**的轨迹律 `Measure (Traj (Fin T) X)` = `unfold_#(D₀ ⊗ D_ε^{⊗T})`；`ℕ`/`ℝ≥0` 视窗**未构造**（文件自述需 Kolmogorov 扩张，Mathlib 无封装）；`trajLaw` 类型**未带 `IsProbabilityMeasure`**（两相关文件 `grep -c` 均 0） | 🟡 **部分** |
| **1.2** | `F_traj` 的定义域与值域可测性 | 「σ-代数、可测结构、`F_traj` 的可测性，本章均未给出」 | **⟳ 旧判「❌ 未实现」，错。** 存在**逐字引用净版 `:158` 专为此问题写的模块** `Fate/TrajGenMeasurable.lean`：`trajGen_measurable_at`(`:138`)、`trajGen_measurable`(`:181`) 已证；定义域取 `InputSeq F`(`:109`)=三序列乘积、值域取 Pi 可测空间。**但条件是 5 条 `MeasurableSpace` + 单步 `f` 联合可测，且 `θ`/`x₀` 作定义域部分未做，文件自述「**不**声称 1.2 已解决」** | 🟡 **部分** ⟳ |
| **1.3** | 因果事件 `e_i` 与状态 `x_t` 的关系 | 「**从未定义**因果事件与状态 `x_t` 的关系」 | `CausalEvent`/`causalEvent` 全库**零命中**（「因果事件」这个对象不存在）；但净版列的第三候选「**是转移 `f` 的一次施加**」已由 `SCMWorldModel.scmWorldModel_sim_succ`(`:408`, `rfl` 级 `sim (n+1) = (sg (u n)).2 (a n)`) 落地。**「已知 1.3」的宏观反馈条件概率在 Lean 里无处对应** | 🟡 **部分** ⟳ |
| **1.4** | 「路径依赖」的形式定义 | 「**从未形式化**」 | 三候选逐条查：① `x_t` 对 `x₀` 连续依赖 ❌（`PathDep` 零命中）；② 多稳态分区 ❌（`MultiStable`/`multistable`/`Bistable` 零命中）；③ 记忆 ❌（`Step F := X → U → Ν → Θ → Act → X`，`Frame.lean:150`，**签名里只有当前状态**）。唯一沾边 `MainLoop.hysteresis_no_self_resume`(`:328`) 是**循环状态机**的锁存，与 `x_t` 轨迹无关 | ❌ **未实现** |
| **1.5** | `θ`、`x_0` 之外的第三种候选 | 「未给出证明」 | `grep -rn 'PathDep' Fate/` **零命中**。补充结构性理由：`Frame` 只有 5 字段（`Frame.lean:73-83`，`Θ/X/U/Act/Ν`），`x₀` 都不在其中（在 `TrajGen` 签名里作输入），「再并列一个给定项」**在类型层无落点** | ❌ **未实现** |
| **2.1** | `u_t` 与 `ε_t` 的类型区分 | 「原素材从未区分」 | **`Frame` 三条独立字段**：`U : InputSpace`(`:79`)、`Act : ActionSpace`(`:81`)、`Ν : NoiseSpace`(`:83`)；`Step` 签名 `… → U.Carrier → Ν.Carrier → …`(`:150`) **参数位不同**；`Yun F := U.Carrier × Ν.Carrier`(`:110`)；`TrajGenStochastic.trajLaw` 的输入位有 `(ι → U)` 但**无** `(ι → Ν)`（噪声积成 `Dε : Dist F.Ν`）⟹ 二者进入 `f` 的方式**确实不同** | ✅ **已实现**（见 §2 的限定） |
| **2.2** | `a_t` 与 `u_t` 的关系（分解存在性） | 「该分解**是否总是存在**，以及 `a_t` 与 `ũ_t` 的取值空间是否独立，原素材未给」 | **⟳ 旧判「❌ 未实现」已过时。** HEAD `6b6d0f4` 新入链 `Fate/ActInputDecomp.lean`（11 定理）：`exists_decomp_iff`(`:283`) 给出**充要条件**「可升级为 `FrameWithDecomp` ⟺ 存在带左逆的单射 `Act → U`」；`noEmbedCounterFrame`(`:161`)+`noEmbed_counterFrame`(`:180`) 给出**具体反例**（`Act=Unit, U=Empty`）⟹ 「总是存在」= **否**；`FrameWithDecomp`(`:223`) 下分解**可构造**（`decomp_B_identifiable` `:254`）。**第二问（`a_t` 与 `ũ_t` 取值空间是否独立）文件自述未答** | 🟡 **部分** ⟳ |
| **2.3** | 「慢」的阈值 | 「该判据中的 `≪` 没有阈值」 | **⟳ 旧判「🟡 部分，行号待细查」现给出精确答案。** `Frame.lean:595-604` 逐字登载**作者裁决 Q-1**，并明写「**该裁决废除了**……(b) 带阈值 `ε=τ_fast/τ_slow`」（`:596-600` 划删除线）。新判据：`ThetaStableOn`(`:626`，「θ 在提取样本上取常值」，**不需阈值**）+ 定量版 `ThetaStableWithin`(`ThetaStabilityMetric.lean:50`)。`ε₀`/`τ_fast`/`τ_slow` 在 Lean 全库**零命中** | ⚠ **净版已过时** ⟳ |
| **2.4** | 「命显／命隐」判据 | 「该判据**从未定义**」 | 净版 `:25` 明写「『命显／命隐 × 运顺／运逆』四象限策略表……**均已删除且不得回流**」；`:730` 自注「四象限表（**已随约定 2.7 废止**）」；`:3379` 同。Lean 侧 `Manifest`/`Hidden`/「命显」零命中——**这是正确行为，不是缺陷** | ⚠ **净版已过时** |
| **5.1** | **∘ 的语义** | 「是前后相接、是条件分布的边缘化、还是规则集的并？原文未给」 | ✅ **已裁决（第 465 轮）并实施**：`ComposeUnified`（7 定理，`Fate.lean:936` 在链），含 `B_is_commutative`(`:201`)、`A_not_commutative`(`:249`)、`B_dominates`(`:267`)、`fusion_structure`(`:289`)、`two_instances_under_one_abstraction`(`:312`) | ✅ **已裁决+实施** |
| **5.2** | 结构性指标（唯一性/稳定性/可恢复性） | 「未定义」；后果栏写「**规则**无质量度量」 | **⟳ 旧判「✅ 已实现（5 个模块）」过宽，已收窄。** 逐指标查：「**稳定性**」✅ 有，但是 **θ 的**（`ThetaStableOn` `Frame.lean:626` + `ThetaStableWithin` `ThetaStabilityMetric.lean:50` + `stable_iff_stableWithin_zero` `:92`），**不是规则的**；「**唯一性**」🟡 只在**局部域划分**（`AlphaSpec.partition_eq_iff` `InstanceChain.lean:259`）与 **σ 的误差界**（`SigmaGammaFromData.profData_unique_boundary`）上有；「**可恢复性**」❌ `Recoverab` **零命中**（`KernelQuotientRecovery` 的 `Recovery` 是「三套结构回收成一般理论的特例」，**名字像而语义完全不同**） | 🟡 **部分** ⟳ |
| **5.3** | 等价关系 `∼_E` 的判据 | 「『两个实例何时算同一个等价类』的判据原文未给出」 | **两套都在，且都可计算**：① `AlphaSpec` 五条 S1–S5(`InstanceChain.lean:216-227`) + 三律 `class_refl`(`:235`)/`class_symm`(`:240`)/`class_trans`(`:245`) + **`partition_eq_iff`(`:259`)**（同类 ⟺ 同一局部域）；配 `closedPartition`（`AlphaMVFCA:72`）+ `RulesLocal (closedPartition K)`（`AlphaRulesLocal:103`）+ **完整实例** `alphaOf_spec`(`AlphaOf:69`)；② `AlphaKernel.alphaKernel`(`:58-66`) —— **作者授权 Q-3 的正式消解**，文件头 `:60-64` 明写「Q-3 状态：悬置 → **✅ 消解**」，判据 = `α(enc ·)` 的核 | ✅ **已实现** |
| **5.4** | 编码算子 `enc: x_t ↦ (A_t, B_t)` **及其误差界** | 「未给」⟹ 后果「FCA 不得进入规则层主链」 | **⟳ 旧判「🟡 部分」方向对，但证据要换。** 本报告**不采用**旧版的 `enc3 : Encoder frame3 K3`（`AlphaConcreteInstance:365`）作为主证，改用**权威定义点**：`Alpha.lean:111` `structure Encoder`（`toObjects : X → Set GFCA`、`toAttrs : X → Set MFCA`）+ `Encoder.Coherent`(`:134`，`toObjects x = polarDown (toAttrs x)`)。**误差界确实不存在**：`Alpha.lean:110` 自述「『误差有界』一半**未做**」，`Stage0/LabelAudit.lean:1329` 独立复核「**后半『误差有界』不存在**」 | 🟡 **部分**（一半✅一半❌） |
| **5.5** | FCA 导出算子与 `α` 的关系 | 「**未建立**……『形式上的相似』不得写作『同构』或『同一个抽象算子的不同实例』。原文『……是同一个抽象算子的不同实例』——**该全称断言废止**」（`净版:2105` 全文已核） | **⟳ 旧判「🟡 部分」的理由需精确化。** 净版在此禁止两件事：(a) 「**未给出映射**」；(b) 「不得写作**同构/同一算子**」。Lean 把 (a) **完全满足**且超出：`polarUp_eq`(`:129`)/`polarDown_eq`(`:121`)/`takeConcept_eq_closureOp`(`:168`) 给出恒等映射，`alpha`(`:358`) 定义为 `(instanceConcept, takeConcept ∘ obs)`，`alpha_snd_eq_thIter`(`:384`) 证**有限步可算**；`AlphaAndStochasticWiring:235` `gc_polarUp_polarDown` 证 Galois 连接，`:249/:254/:259` 三条 hexagon；且已被消费（`WorldModelCompleteV2.alpha`(`:164`) 字段类型 + Wiring 10 条 `AlphaData.*` 定理）。**但「同构/同一算子」这条禁令 Lean 未越线**（无任何 `Iso`/`≅` 断言）⟹ **净版的 5.5 内容已被完整覆盖** | ✅ **已实现** ⟳ |
| **5.6** | `C` 的结构 | 「上下文依赖无判据」 | **⟳ 旧判「✅ 已实现（`Frame:292` 有 `structure CtxSpace`）」是错的：`CtxSpace` 只有 `Carrier : Type*`，没有任何结构约束**。实际有 **4 个具体实现**：`CtxParts`（`Local × U × Act × Θ`，`InstanceChain.lean:73-85`）、`RichCtx`（`U × Ν × Θ × Act`，`LawRuleToTraj.lean:411`）、`FormalCtx`（`FCA.lean:92`）、`TieredScheme` 分档；全库 **23 处** `CtxSpace where`。**但主结构取 `⟨PUnit⟩`（`WorldModelCompleteV2.lean:140-143`「**刻意的退化**」，登记 U4）** ⟹ 主干上的上下文依赖**仍未闭合** | 🟡 **部分** ⟳ |
| **5.7** | 覆盖率/准确率/简洁度公式 | 「定义 5.4 只三个量可用」 | **⟳ 旧判「🟡 部分，语义待核实」现已核实：「名字像而语义不同」。** 覆盖率有两个，**都不是净版要的**：`AlphaStatistical.Coverage`(`:320`) = 「每格位样本量 `n(c,x) ≥ n_min`」（**采样覆盖**，配 `IsPoint ⟺ Coverage ∧ BandCollapse` `:585`）；`ICPCoverage.icp_coverage`(`:109`) = **ICP 预测集包含真因果父集的概率下界**（并显式化论文隐藏前件 `Prob.compl_add` `:84`）。**「准确率」「简洁度」零命中** | 🟡 **部分**（1/3 且非同一量） |
| **6.10** | 效应估计只给组平均，个体轨迹不可推出 | 「个体命运轨迹不可由它推出」；「**明确禁止**用 ATE/CATE 的数值直接陈述任何个体的命运」 | **⟳ 第 476 轮修正记录已在案：旧判「零命中」不准。本轮复核：`ATE`/`CATE`/`ITE`/`treatment`/`averageTreatment` 作为概念**确实零命中**（此前 6 个文件的 `cate` 命中全是 `DERIVATIVE`/`INDICATE`/`LOCATE` 类**子串误匹配**）。反事实模块**有 7 个**且 `CounterfactualStrictness.cf_strictly_weaker_than_eq` 为真内容；`CfPartialIdent` 给**个体层区间**；`ErrorCriterionImpliesBound:221` 给**个体粒度**的分类正确（`sgn : ℝ → ℤ`）。⟹ 「组平均 → 个体不可推」**既未被违反也未被证明，因为它所担心的对象不存在** | ⚠ **净版已过时**（见 §2 的降级说明） ⟳ |

---

## 二、统计

### 2.1 第 478 轮最终判定（16 条 + 5.1）

> 任务书核查的是**除 5.1 外的 16 条**（5.1 已裁决）。下表把 5.1 单列，不改任务书的 16 分母。

| 判定 | 个数（/16） | 条目 |
|---|---|---|
| ✅ **已实现** | **3** | 2.1、5.3、5.5 |
| 🟡 **部分实现** | **8** | 1.1、1.2、1.3、2.2、5.2、5.4、5.6、5.7 |
| ❌ **未实现** | **2** | 1.4、1.5 |
| ⚠ **净版已过时（问题已不成立）** | **3** | 2.3、2.4、6.10 |
| **合计** | **16** | ✔ 3+8+2+3 = 16 |

**另有 5.1（∘ 的语义）= ✅ 已裁决+实施**（不计入 16）。
**⟹ 17 条中已有实质落地的：3 + 1 = 4 条 ✅；8 条 🟡；2 条 ❌；3 条 ⚠。**

### 2.2 与历次判定的演进（保留历史，防「反复横跳」）

| 条目 | 第 474 轮（主控快速版） | 第 476 轮修正 | 第 477 轮修正 | **第 478 轮（本轮，实查）** |
|---|---|---|---|---|
| 1.2 | ❌ | — | — | **🟡**（发现 `TrajGenMeasurable`；旧版只看 `TrajGenDeterministic` 的 `Measurable` 计数=0，**查错了文件**） |
| 1.3 | ❌ | — | — | **🟡**（`SCMWorldModel` 落了第三候选） |
| 2.2 | 🟡 | — | ❌（「分开了」≠「分解存在」） | **🟡**（`ActInputDecomp` 入链；旧❌已过时） |
| 2.3 | 🟡 | — | — | **⚠**（Q-1 已废除阈值判据） |
| 5.2 | ✅（5 模块） | — | — | **🟡**（旧版把「可识别性」当「结构性指标」，过宽） |
| 5.5 | ✅ | — | 🟡（净版禁的是「同构」） | **✅**（净版禁两事：未给映射 / 写作同构。前者已满足且超出，后者未越线 ⟹ 5.5 内容被覆盖） |
| 5.6 | ✅（`Frame:292`） | — | — | **🟡**（`CtxSpace` 只有 `Carrier`；主结构用 `PUnit`） |
| 5.7 | 🟡 | — | — | **🟡**（语义已核实为不同量） |
| 6.10 | ❌ | 🟡 | 🟡 | **⚠**（对象不存在；降级理由见 §3） |

**净变化**：✅ 6→4（含 5.1 则 4）、🟡 5→8、❌ 5→2、⚠ 1→3。
**⟹ 变化方向是「❌ 减少、⚠ 增加」**：查得越细，越多条目从「没做」变成「**已被换了问题**」或「**部分做了**」。
这与作者第 388 轮原话「**部分裁决是有问题的它没看具体的 lean 很多是已经实现掉了的**」方向一致，**但不是靠「发现更多实现」而是靠「发现净版的问题设定已被改动」**。

---

## 三、逐条核查（证据与理由）

> 只列**判定有争议或旧版需更正**的条目。1.4、1.5、2.4、5.1 证据直接见汇总表。

### 1.1 路径空间的测度 —— 🟡 部分

**净版原文**（`净版:127`）：
> 当 `T = ℝ≥0` 且状态为随机变量时，「随机过程的样本路径」要求先给定一个函数空间及其上的 σ-代数与概率测度……原素材**从未给出该路径空间与其上的测度**。

**实测**：

```
$ grep -rn 'SamplePath|pathSpace|PathSpace|TrajSpace|trajSpace|samplePath' Fate/
（零命中）

$ grep -rln 'PathMeasure|TrajMeasure|trajMeasure|trajLaw|TrajLaw' Fate/
Fate/TrajGenStochastic.lean
Fate/AlphaAndStochasticWiring.lean

$ grep -n 'def trajLaw' -A8 Fate/TrajGenStochastic.lean
201:def trajLaw (F : Frame) [MeasurableSpace F.Ν.Carrier]
202-    [MeasurableSpace F.X.Carrier] (f : Step F) (T : ℕ)
203-    (D0 : InitDist F) (Dε : Dist F.Ν) (θ : F.Θ.Carrier)
204-    (u : Fin T → F.U.Carrier) (a : Fin T → F.Act.Carrier) :
205-    MeasureTheory.Measure (Traj (Fin T) F.X) :=
206-  Measure.map (unfold F f T θ u a)
207-    (D0.prod (MeasureTheory.Measure.pi (fun _ : Fin T => Dε)))

$ grep -c -e IsProbabilityMeasure Fate/TrajGenStochastic.lean Fate/AlphaAndStochasticWiring.lean
Fate/TrajGenStochastic.lean:0
Fate/AlphaAndStochasticWiring.lean:0

$ grep -n 'def iidMeasure' -A2 Fate/SigmaEstimation.lean
72:noncomputable def iidMeasure (P : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
73-  Measure.pi (fun _ : Fin n => P)
```

**找到的实现**：`TrajGenStochastic.lean`（`Fate.lean:62` 在链）——`InitDist`(`:70`)、`NoiseSeqMeasure`(`:82`)、
`IidNoise`(`:93`，把 i.i.d. 做成可见 `Prop` 前件)、`xNextDist`(`:113`)、**`trajLaw`(`:201`)**、`trajGenSto`(`:232`)；
`AlphaAndStochasticWiring.trajLaw_dirac`(`:419`)/`dirac_collapse_both_levels`(`:451`) 给出**测度层塌缩**。

**⚠ 关于任务书线索「`iidMeasure` 是不是路径空间的测度」——不是。**
`iidMeasure P n : Measure (Fin n → ℝ)` 是 **`n` 个 i.i.d. 实值样本**的乘积测度，
用于对**估计器**算方差（`variance (steadyErrEst η n) (iidMeasure P n)`，`SteadyErrEstimate.lean:170`）。
它与轨迹空间 `Traj (Fin T) F.X = Fin T → F.X.Carrier` 只在**形状上**同构（都是 `Fin n → ·`），
**索引语义不同**（样本索引 vs 时间索引）、**对象不同**（估计器输入 vs 世界轨迹）。⟹ **名字/形状像，语义不同。**

**判定理由（三层）**：
1. **有限视窗上已经有了**：`trajLaw` 就是一个 `Measure (Traj (Fin T) X)`，由 `D₀ ⊗ D_ε^{⊗T}` 推前得到，
   正是「随机过程 = 样本路径上的分布」。⟹ 净版「轨迹的分布无定义」在 `Fin T` 上**已不成立**。
2. **`ℕ`/`ℝ≥0` 视窗缺失且有理有据**：`TrajGenStochastic.lean:37-41`「`Measure.pi` 在 Mathlib 中要求**有限**索引……
   无穷索引需 Kolmogorov 扩张定理，属**外部理论**，本文件**不使用**、**不假设**」；§7 末再写「该定理在本项目的 Mathlib 检出中**未找到可直接调用的封装**」。净版问的 `T = ℝ≥0` 是**连续时间**，比 `ℕ` 更远。
3. **`trajLaw` 的类型不含 `IsProbabilityMeasure`**：两相关文件 `grep -c` 均 **0**。
   ⟹ 数学上它是概率测度（prod of probability measures 的 `Measure.map`），但**类型/定理层无证据钉住**，
   下游无法 `haveI := ...` 地使用。**该点是否在第三处被证明——未核实（未做全库 `grep`）。**

---

### 1.2 `F_traj` 的可测性 —— 🟡 部分（**旧判 ❌ 是查错文件所致**）

**净版原文**（`净版:158`）。**旧判依据**：「`trajGen` 存在（`TrajGenDeterministic:39/56/57`），但该文件 `Measurable` 出现 **0 次**」。
**这个观察是对的，但结论错了** —— `Measurable` 不在 `TrajGenDeterministic` 里，而在**另一个专为 1.2 写的文件**里。

**实测**：

```
$ head -14 Fate/TrajGenMeasurable.lean
命运理论 · 开放问题 1.2：`F_traj`（`trajGen`）的可测性 —— 条件性结果
模块：Fate.TrajGenMeasurable
---
(a) 净版开放问题 1.2 原文（`10-命运理论-净版.md:158`）
> **[开放问题] 开放问题 1.2（`F_traj` 的定义域与值域）**
> `F_traj` 的定义域含序列 `{u_t}`、`{ε_t}`、`{a_t}`，其值域是轨迹空间。
> **该定义域上的 σ-代数、值域上的可测结构、以及 `F_traj` 的可测性，本章均未给出。**

$ grep -n -e '^theorem' Fate/TrajGenMeasurable.lean
138:theorem trajGen_measurable_at
181:theorem trajGen_measurable
197:theorem const_jointMeasurable
207:theorem fst_jointMeasurable

$ grep -n InputSeq Fate/TrajGenMeasurable.lean
109:abbrev InputSeq (F : Frame) : Type _ :=
115-121 (5 条 variable [MeasurableSpace ...])
```

**找到的实现**（`Fate/TrajGenMeasurable.lean`）：

| 净版问的 | Lean 的答 | 行 |
|---|---|---|
| 定义域上的 σ-代数 | `InputSeq F := (ℕ→U) × (ℕ→Ν) × (ℕ→Act)` 配**乘积 Pi 可测结构**；5 条 `MeasurableSpace` 作显式前件（不改 `Frame`） | `:109`、`:115-121` |
| 值域上的可测结构 | `Traj ℕ F.X`（`= ℕ → F.X.Carrier`）配 **Pi 可测空间**（文件自述是**显式的建模选择**） | `:181` 陈述 |
| `F_traj` 可测性（逐点） | `trajGen_measurable_at` | `:138` |
| `F_traj` 可测性（整条） | `trajGen_measurable` | `:181` |
| 前件**非空真** | `const_jointMeasurable` / `fst_jointMeasurable` | `:197` / `:207` |

**判定：🟡 部分。** 三条被问的东西**都给了答案**，但：
> `:76`「5. **没有**声称『开放问题 1.2 已解决』。」
> `:87`「**不**声称『开放问题 1.2 已解决』。」
> `:68-71`「3. **没有**解决『定义域上的 σ-代数』的**唯一性 / 正确性**问题：……净版问的是『该取什么』，本文件**回答是『取这个能证』**，而**不是**论证它是对的那个。」
> `:74-76`「4. **没有**处理 `θ`、`x₀` 也作为**变量**时的可测性」

**为什么不能判 ✅**：净版 `F_traj` 的定义域是**五元组** `(θ, x₀, {u_t},{ε_t},{a_t})`（见 `Frame.lean:157-162` 的 `TrajGen` 签名）。
Lean 做的是 **3/5**（`u`、`ε`、`a`），`θ`/`x₀` 明文未做。
且「定义域 σ-代数」Lean 给的是「一个可用的选择」，净版要的是「定下来的那个」——**不是同一件事**。

---

### 1.3 因果事件 `e_i` 与状态 `x_t` —— 🟡 部分（**换了一种定义方式接上**）

**实测**：

```
$ grep -rn 'CausalEvent|causalEvent' Fate/ --include=*.lean
（零命中）

$ grep -n -e '^theorem' Fate/SCMWorldModel.lean | head -6
385:theorem scmWorldModel_f {X Y : Type} (M : SCM X Y) [Nonempty Y] :
408:theorem scmWorldModel_sim_succ {X Y : Type} (M : SCM X Y) [Nonempty Y]
457:theorem scmWorldModel_doLaw_eq_push_step (M : SCM X Y)
483:theorem scmWorldModel_jointLaw_eq_sim (M : SCM X Y) [Nonempty Y]
531:theorem scmWorldModel_doLaw_eq_sim (M : SCM X Y) [Nonempty Y]
574:theorem scmWorldModel_wellFormed (M : SCM X Y) [Nonempty Y] :
```

净版给了**三个候选读法**：「是 `x_t` 的取值？是变量集 `V` 的子集上的赋值？**是转移 `f` 的一次施加**？」
第三个读法被 `SCMWorldModel` 坐实：

```
408:theorem scmWorldModel_sim_succ ... :
    (scmWorldModel M).sim θ u ε a (n + 1) = (M.sg (u n)).2 (a n)
```
即「SCM 的一次外生实现 + 一次干预 ⟹ 一步状态」。配 `scmWorldModel_doLaw_eq_sim`(`:531`)、
`scmWorldModel_jointLaw_eq_sim`(`:483`)、`scmWorldModel_marginalY_eq_sim`(`:503`)，
把干预律 / 联合律 / 边缘律都接到 `sim` 的轨迹上。

**判定：🟡 部分。必须严格区分两件事**：
- **❌ 真的没有**：「**因果事件**」这个对象在 Lean 里不存在（零命中），也没有「`e_i, e_j` 两个事件的取值空间」；
  净版「已知 1.3」的条件概率式 `P(e_j | e_i, {x_τ}_{τ≤t}) ≠ P(e_j | e_i)`（`净版:1243`）**在 Lean 里无处对应**。
- **✅ 部分有**：「`e_i` = 转移 `f` 的一次施加」这一读法被 `SCMWorldModel` 实现到了可证程度，
  只是它不用 `e_i` 这个名字，用 `(u n, a n)` 这一对。
  ⟹ **把它写成「1.3 已实现」是夸大**；写成「完全未实现」是漏读。

---

### 2.1 `u_t` 与 `ε_t` 的类型区分 —— ✅ 已实现

```
$ sed -n '73,83p' Fate/Frame.lean
73:structure Frame where
75-  Θ : ThetaSpace
77-  X : StateSpace
79-  U : InputSpace
81-  Act : ActionSpace
83-  Ν : NoiseSpace

$ sed -n '110,111p;147,151p' Fate/Frame.lean
110:def Yun (F : Frame) : Type _ := F.U.Carrier × F.Ν.Carrier
147:abbrev Step (F : Frame) : Type _ :=
150-  F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier → F.X.Carrier
```

净版原话是「原素材**从未区分**」「未说明二者**是否可互换位置**」。
Lean 不但区分类型，还**用类型系统强制不可互换**（不同 `Type` 字段 + 不同参数位）——这正是「可互换位置」的**否定**。
`TrajGenStochastic.trajLaw`(`:202-204`) 更进一步：输入位有 `(ι → U)` 但**无** `(ι → Ν)`（噪声积成 `Dε : Dist F.Ν`），
即 **`u_t` 保持「确定的序列」，`ε_t` 变成「分布」——二者进入 `f` 的方式确实不同**。

**诚实边界（否则会高估）**：净版 2.1 还有一半是「`u_t` **是否也是随机变量**」（`净版:582` 说明 2.7）。
Lean 里 `U` 是确定性类型（无测度），`TrajGenStochastic` 也**不**给 `U` 加分布——
**这是「选了确定性」这一读法，不是「回答了它是否随机」**（`Frame.lean:100-108` 登记为定义性约定）。
`grep` 控制/噪声区分的更深谓词（`IsControlDeterministic`/`ControlNoise`/`NoiseVsControl`）**零命中**。
⟹ ✅ 是对「区分 + 不可互换」这一问；对「`u_t` 是否随机」是**取了约定**而非证明。

---

### 2.2 `a_t` 与 `u_t` 的分解 —— 🟡 部分（**旧判 ❌ 已过时**）

**⚠ 本条在核查期间被一个新入链模块正面处理。** `git log -1` → `6b6d0f4 feat: ActInputDecomp 入链（11 定理）—— 开放问题 2.2 的完整回答`。

```
$ grep -n -e '^theorem' -e '^def' -e '^structure' Fate/ActInputDecomp.lean
111:theorem actInput_pair_bijective (F : Frame) :
126:theorem actInput_pair_surjective (F : Frame) :
140:theorem actInput_const_map_of_nonempty (F : Frame)
161:def noEmbedCounterFrame : Frame where
180:theorem noEmbed_counterFrame :
192:theorem not_forall_embed :
223:structure FrameWithDecomp extends Frame where
240:theorem decomp_B_holds (F : FrameWithDecomp) :
254:theorem decomp_B_identifiable (F : FrameWithDecomp) :
266:theorem retract_surjective (F : FrameWithDecomp) :
283:theorem exists_decomp_iff (F : Frame) :
301:theorem counterFrame_no_decomp :
323:theorem open22_status :
```

| 净版的问题 | Lean 的答案 | 定理 |
|---|---|---|
| 「分解是否**总是**存在？」 | **否**。具体反例 `noEmbedCounterFrame`（`Act=Unit, U=Empty`） | `:161`/`:180`/`:192` |
| 「存在的**充要条件**？」 | **⟺ 存在带左逆的单射 `Act → U`**（「可分辨」+「可反读出」） | `exists_decomp_iff`(`:283`) |
| 「**加什么结构**才成立？」 | `structure FrameWithDecomp extends Frame`（`embed` 单射 + `retract` + `LeftInverse retract embed`） | `:223` |
| 该结构下分解**可构造**？ | 是 | `decomp_B_holds`(`:240`)、`decomp_B_identifiable`(`:254`) |
| 反例**可升级**？ | **不可能** | `counterFrame_no_decomp`(`:301`) |

**判定：🟡 部分（高完成度的部分）。** 理由：
- 净版问**两问**：① 是否总是存在；② `a_t` 与 `ũ_t` 取值空间是否独立。
- **①被完整回答**，且非平凡（**否** + 充要条件 + 具体反例 + 加结构后的正例），远强于「未给」。
- **②未被回答**。文件自述（`:70-72`）：「**未**讨论 `a_t` 与 `ũ_t` 取值空间是否独立（净版同时问的第二问）—— 本结构只给出『`Act` 经嵌入落在 `U` 内』，对 `ũ_t` 的取值空间**不作断言**。」
- 文件**自己拒绝声称已解决**（`:65`「**本文件【不】声称『开放问题 2.2 已解决』**」；`:323` `open22_status` 注解「**本定理不是『开放问题已解决』的声明**」）。

**⚠ 关于 commit message 的「完整回答」**：按定理内容，**它回答的是第一问（且给了充要条件），第二问明确未答**。
**「完整」应读作「对该模块所承担的那一问的完整回答」，不等于净版 2.2 整体已解决。**
**另需排除一个「名字像」**：`Stage0/Core.lean:413` 也有 `InputSpace.decompose : U → Action 𝒜 × Ũ`，
但它**不主张**是分解（`:419-421`「分开给出，**不主张**二者互逆」），`Ũ` 是**自由参数**（`:404-406`）。
**`Stage0/Core.decompose` 不是 2.2 的答案。**

---

### 2.3 「慢」的阈值 —— ⚠ 净版已过时

**实测（这是本任务里最需要「拿证据改净版」的一条）**：

```
$ sed -n '583,604p' Fate/Frame.lean
-  ~~(b) 带阈值 $\epsilon=\tau_{\text{fast}}/\tau_{\text{slow}}$~~
**该裁决废除了**实现代理此前登记的两个选项：
- ~~(a) 时不变（$\dot\theta=0$）~~
- ~~(b) 带阈值 $\epsilon=\tau_{\text{fast}}/\tau_{\text{slow}}$~~
$\theta$ **不是先验给定的参数**，而是由某个**提取过程**从实例集得到的输出。

$ sed -n '608,628p' Fate/Frame.lean
**⚠ 待裁决**：样本集 $S$ 的选取（大小、代表性）**未被作者裁决**…（规格明写「填数即为虚构」）
def ThetaStableOn {E : InstSpace} {Θ : ThetaSpace} (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) : Prop :=
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, ext.extract e₁ = ext.extract e₂

$ grep -n -e 'def ThetaStableWithin' -A3 Fate/ThetaStabilityMetric.lean
50:def ThetaStableWithin [PseudoMetricSpace Θ.Carrier]
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) (ε : ℝ) : Prop :=
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, dist (ext.extract e₁) (ext.extract e₂) ≤ ε
92:theorem stable_iff_stableWithin_zero [MetricSpace Θ.Carrier]
```

`Frame.lean:612-618` 的对照表（逐字）：

| | 旧读法（**已废除**） | 新定义（作者裁决 Q-1） |
|---|---|---|
| 判据 | `‖θ̇‖ ≪ ‖ẋ‖` 或阈值 `ε` | **样本上取常值** |
| 类型 | **动力学**（时间尺度分离） | **统计/提取**（样本一致性） |
| 是否需要数据 | **不需要**（可先验陈述） | **必须有数据** |

**判定：⚠ 净版已过时。** 理由：
1. 净版 2.3 断言「**判据不可判定**，因为阈值 `ε₀` 未给」。
2. Lean 侧**作者裁决 Q-1 直接废除了「以阈值为判据」这条路线**（`Frame.lean:596-600` 划删除线），
   换成一条**根本不需要阈值**的判据：`ThetaStableOn`(`:626`) + 定量版 `ThetaStableWithin`(`ThetaStabilityMetric.lean:50`)。
3. **⚠ 一个极易混的「名字像」**：`ThetaStableWithin` 里的 `ε` **不是**净版的 `ε₀`（时间尺度分离阈值），
   而是「**参数距离容差**」，作用于 **$Θ$ 空间**；净版 `ε₀ = τ_fast/τ_slow` 作用于**时间尺度**。**二者完全不同量纲，勿混。**
4. `ε₀`/`τ_fast`/`τ_slow`/`SeparationParam`/`Epsilon0` 在 Lean 全库**零命中**，佐证「时间尺度分离这条线在 Lean 里根本没被实现」。
5. ⟹ 净版 2.3 作为「待裁决开放问题」**已不再有效**（前提被裁决推翻），但**没有变成「已实现」**——是「**问题被换了**」。**净版这条必须重写。**

---

### 5.2 结构性指标 —— 🟡 部分（**旧判 ✅ 过宽**）

**实测**：

```
$ grep -rln 'Recoverab|recoverab|IsUnique|uniqueRule|StableEq|Stability' Fate/
Fate/InterventionSelection.lean
Fate/ThetaStabilityMetric.lean

$ grep -rn 'Recoverab|recoverab' Fate/
（零命中）

$ ls Fate/ | grep -i -e unique -e recover -e identif
KernelQuotientRecovery.lean  SCMIdentifiabilityCorrect.lean
SCMIdentifiability.lean  T314Identifiability.lean  ThetaStabilityMetric.lean
```

| 指标 | 有无 | 证据 / 说明 |
|---|---|---|
| **稳定性** | ✅ **有（两版），但是 θ 的** | `ThetaStableOn`(`Frame.lean:626`)、`ThetaStableWithin`(`ThetaStabilityMetric.lean:50`)、关系 `stable_iff_stableWithin_zero`(`:92`)，且**分 `PseudoMetricSpace`/`MetricSpace` 两个方向**（`:61`/`:76`）——这是真实的数学细致性（伪度量下 `dist a b = 0` 不推 `a = b`） |
| **唯一性** | 🟡 **只在两处别的地方** | 局部域划分：`AlphaSpec.partition_eq_iff`(`InstanceChain.lean:259`)；σ 的误差界：`SigmaGammaFromData.profData_unique_boundary` |
| **可恢复性** | ❌ **无** | `Recoverab` 零命中。`KernelQuotientRecovery` 的 `Recovery` 是「把三套结构**回收**成一般理论的特例」（文件头 `:8-12` 表格），**不是「规则可恢复」**——**名字像而语义完全不同** |

**判定：🟡 部分。** 净版 5.2 的三个词都挂在**「规则」**上（`净版:2130` 后果栏：「**规则**无质量度量」）。
Lean 里的「稳定性」挂在 **θ** 上（Q-1 的提取稳定性），**不是规则**。
⟹ **严格讲，「规则的结构性指标」三项全缺**；宽松讲，「稳定性」这一概念已被形式化（换了载体）。判 🟡 并在文档中写明这个歧义。

**⟳ 旧判「✅ 已实现（`SCMIdentifiability`/`T314Identifiability` 等 5 模块）」为何过宽**：
那些模块做的是「**因果结构可识别性**」（从观测分布能否唯一确定因果图/SCM），
这是**因果发现的识别问题**，与净版 5.2 说的「**规则**的唯一性/稳定性/可恢复性」**不是同一个概念**。

---

### 5.3 `∼_E` 的判据 —— ✅ 已实现

```
$ grep -rn 'AlphaSpec|closedPartition' Fate/ --include=*.lean | head -8
Fate/InstanceChain.lean:216:structure AlphaSpec {D : Type u} {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
Fate/InstanceChain.lean:235:theorem AlphaSpec.class_refl
Fate/InstanceChain.lean:240:theorem AlphaSpec.class_symm
Fate/InstanceChain.lean:245:theorem AlphaSpec.class_trans
Fate/InstanceChain.lean:259:theorem AlphaSpec.partition_eq_iff
Fate/AlphaOf.lean:69:theorem alphaOf_spec
Fate/AlphaRulesLocal.lean:103:  InstanceChain.RulesLocal (closedPartition K)

$ sed -n '216,232p' Fate/InstanceChain.lean
216:structure AlphaSpec ... where
219-  covers : ∀ d, PartitionCovers (α d).partition
221-  part_symm : ∀ d, PartitionSymm (α d).partition
223-  part_trans : ∀ d, PartitionTrans (α d).partition
225-  localize : ∀ d, RulesLocal (α d).partition (α d).rules
227-  inhabited : ∀ d, RulesInhabited (α d).rules

$ sed -n '58,66p' Fate/AlphaKernel.lean
58:def alphaKernel (enc : Encoder F K) (E : InstSpace) (embed : E.Carrier → F.X.Carrier) :
59-    Setoid E.Carrier where
60-  r := fun e₁ e₂ => K.takeConcept (enc.toAttrs (embed e₁)) = K.takeConcept (enc.toAttrs (embed e₂))
```

**两套判据（都内生、都可计算）**：

**① `InstanceChain.AlphaSpec`**：
`class_refl`(`:235`) / `class_symm`(`:240`) / `class_trans`(`:245`) 三律 +
**`partition_eq_iff`(`:259`)：`(α d).partition x = (α d).partition y ↔ y ∈ (α d).partition x`**
⟹ 「两个实例何时同一等价类」的判据 = **`y ∈ partition x`**（即同一局部域）。
配套具体划分：`closedPartition`（`AlphaMVFCA:72`）+ `RulesLocal (closedPartition K)`（`AlphaRulesLocal:103`）+ **完整实例** `alphaOf_spec`(`AlphaOf:69`)。

**② `AlphaKernel.alphaKernel`**（**作者授权 Q-3 的正式消解**），文件头 `:60-64` 逐字：
> | Q-3 状态 | 悬置 | **✅ 消解** |
> **⚠ 关键**：核是**从 α 算出来的**，故「α 保持它」**自动成立** —— 这不是把一个假设换成另一个，而是**把假设变成定理**。

`:64` 另注「判定 `e₁∼e₂` 即比较两个属性集，属**可判定**操作（在有限属性集上）」。
⟹ 净版担心的「与 5.1 共同阻塞定义 5.13 的可计算化」**已不成立**（5.1 已裁决，且判据本身可判定）。

**诚实边界**：两套判据**互不冲突但不互相推出**（一个是商结构上的划分，一个是 α 的核）；
「二者何时一致」**未见定理**（`grep` 未找到，**未核实是否有**）。
`AlphaOf` 文件头自述其 `α` 实现「**忽略数据集 `d`**」，是**结构闭合**而非**从数据学出划分**——
那属另一条开放问题（8.5「学到档」），不属 5.3。

---

### 5.4 编码算子 + 误差界 —— 🟡 部分（一半 ✅ 一半 ❌）

```
$ sed -n '105,116p' Fate/Alpha.lean
**本定义即 A32 的「存在」一半在定义层的落点。**
「误差有界」一半**未做**（见文件头诚实边界 3）。 -/
111:structure Encoder (F : Frame) (K : FormalCtx.{u,v}) where
113-  toObjects : F.X.Carrier → Set K.GFCA
115-  toAttrs : F.X.Carrier → Set K.MFCA
134:def Encoder.Coherent {F : Frame} {K : FormalCtx.{u,v}} (enc : Encoder F K) : Prop :=
      ∀ x : F.X.Carrier, K.polarDown (enc.toAttrs x) = enc.toObjects x

$ sed -n '1329p' Fate/Stage0/LabelAudit.lean
    gap := "A32 = 「编码算子**存在**」∧「**离散化误差有界**」。实现侧只有前半：`Fate.Alpha:111`
    `structure Encoder` + `Fate/Alpha:134` `Encoder.Coherent`。**后半「误差有界」不存在**……"
```

| 半 | 有无 | 证据 |
|---|---|---|
| **存在性（算子本身）** | ✅ **有** | `Alpha.lean:111` `structure Encoder`（`toObjects`/`toAttrs` = `x_t ↦ (A_t, B_t)` 的精确落点，对应 S2 步骤 `I(e_t,m_j) := [m_j(x_t) = 真]`，见 `:97-99`）+ **自洽条件** `Encoder.Coherent`(`:134`) 与其三个等价条件 |
| **误差界** | ❌ **无** | `Alpha.lean:110` 自述「『误差有界』一半**未做**」；`Stage0/LabelAudit.lean:1329` 独立复核「**后半『误差有界』不存在**」；全库 `grep` 无任何「编码误差界」定理 |

**⚠ 必须排除的两个「名字像」**：

| 候选 | 为什么**不是** 5.4 的误差界 |
|---|---|
| `AlphaStatistical.Coverage`(`:320`) | = 「每格位样本量 `n(c,x) ≥ n_min`」——**采样覆盖条件**，与「状态↔形式概念的离散化误差」**不同量纲** |
| `ICPCoverage.icp_coverage`(`:109`) | = ICP 的**群体层覆盖率界**（`Pr[Ŝ ⊆ S*] ≥ 1-α`），与状态编码**无关** |

**判定：🟡 部分。** 净版这条是**合取式**——「算子**及其**误差界」。
算子有、误差界无，而**误差界恰是「FCA 不得进入规则层主链」这条后果的唯一依据**（`净版:2091`）。
⟹ **净版 5.4 的实质（为什么不能进主链）在 Lean 里仍未回答。**

**⟳ 关于旧版引的 `enc3 : Encoder frame3 K3`（`AlphaConcreteInstance:365`）**：它是**一个具体实例**，
能证明「`Encoder` 这个结构有实例」，但**不能**证明「算子已定义」这件事（那是 `Alpha.lean:111`）。
本报告改用 `Alpha.lean:111` 作主证，更权威。旧版结论「🟡」方向正确。

---

### 5.5 FCA 导出算子与 α —— ✅ 已实现（**净版的禁令逐条核对后未越线**）

**净版原文**（`净版:2103-2105`，全文实核）：
> 定义 5.9 的导入算子 `(·)'` 与假设 5.2 的抽象算子 `α` 之间的关系**未建立**。把 `α` 读作「取 Galois 连接的不动点」是一个**形式上可辩护的类比**，但**尚未给出映射**；「形式上的相似」不得写作「同构」或「同一个抽象算子的不同实例」。原文曾断言「FCA 的 Galois 连接、物理规律的提取、规则学习，是同一个抽象算子的不同实例」——**该全称断言废止**。

**净版在此禁止的是两件事**：
- **(a)「尚未给出映射」** —— 即缺 `(·)'` → `α` 的映射；
- **(b) 不得写作「同构」或「同一算子」**（因为原文的全称断言已废止）。

**实测（逐条对 (a)(b) 核对）**：

```
$ grep -n -e 'polarUp_eq' -e 'polarDown_eq' -e 'takeConcept_eq_closureOp' Fate/AlphaFCAConstruction.lean
121:theorem polarDown_eq (D : AlphaData E M) (B : Set M) :
129:theorem polarUp_eq (D : AlphaData E M) (A : Set E.Carrier) :
168:theorem takeConcept_eq_closureOp (D : AlphaData E M) (B : Set M) :
384:theorem alpha_snd_eq_thIter (D : AlphaData E M) [F : (D.ctx).FiniteAttrs]

$ sed -n '344,345p' Fate/AlphaFCAConstruction.lean
| $B'$ | $\{e\mid B\subseteq\mathrm{obs}(e)\}$ | `polarDown_eq` | `polarDown` |
| $A'$ | $\{m\mid\forall e\in A,\,m\in\mathrm{obs}(e)\}$ | `polarUp_eq` | `polarUp` |

$ sed -n '358,360p' Fate/AlphaFCAConstruction.lean
def alpha (D : AlphaData E M) (e : E.Carrier) :
    Concept E.Carrier M (D.ctx).Irel × Set M :=
  (D.instanceConcept e, D.takeConcept (D.obs e))

$ grep -n -e '^theorem' Fate/AlphaAndStochasticWiring.lean | sed -n '9,18p'
221:theorem AlphaData.takeConcept_eq_adjunction
227:theorem AlphaData.takeConcept_eq_comp
235:theorem AlphaData.gc_polarUp_polarDown
241:theorem AlphaData.polar_adjoint_iff
249:theorem AlphaData.hexagon_left
254:theorem AlphaData.hexagon_right
259:theorem AlphaData.hexagon_middle

$ grep -n -e 'alpha : AlphaData' Fate/WorldModelCompleteV2.lean
164:  alpha : AlphaData.{0} input PUnit
```

| 净版要求 | Lean 的答 | 位置 |
|---|---|---|
| (a) **给出映射** `A'` → α | **`polarUp {e} = obs e`**（极算子落到观测映射上） | `polarUp_eq`(`:129`) |
| (a) **给出映射** `B'` → α | **`polarDown B = {e | B ⊆ obs e}`** | `polarDown_eq`(`:121`) |
| (a) α **就是** `(·)'` 的复合 | `takeConcept` = `closureOp` = `polarUp ∘ polarDown` | `takeConcept_eq_closureOp`(`:168`)、Wiring `:227` |
| (a) α 的**定义性展开** | `α e = (instanceConcept e, takeConcept (obs e))` | `:358` |
| (a) α 的**值域正确** | `alpha_fst_mem_conceptLattice` / `alpha_snd_isClosed` | `:376` / `:382` |
| (a) α **可算** | `alpha_snd_eq_thIter`：`∃ n, (α e).2 = thIter n (obs e)` | `:384` |
| (a) **范畴级证据** | Galois 连接 `gc_polarUp_polarDown`(`:235`) + hexagon 三条(`:249/:254/:259`) | Wiring |
| (b) **不得写作同构** | Lean **没有任何** `Iso`/`≅` 断言；全部是**映射等式**与**伴随** | 全文件 `grep` |
| 是否**被消费** | `WorldModelCompleteV2.alpha : AlphaData`(`:164`) + Wiring 10 条 `AlphaData.*` | 见左 |

**判定：✅ 已实现。**
- **净版 (a)「尚未给出映射」已完全被满足且超出**（不止给了映射，还给了恒等、值域正确、可算性、Galois 连接、hexagon）。
- **净版 (b)「不得写作同构/同一算子」Lean 未越线** —— 这恰恰说明 Lean 的做法与净版**兼容**：
  净版禁止的是「起同一个名字就宣称同一算子」，而 Lean 做的是**给出可验证的映射等式**，不是宣称同构。
- ⟹ **净版 5.5 的实质内容（「关系未建立」）在 Lean 里已不成立。**
- **并且它被消费了**：F1 报告（第 428 轮）说 `AlphaFCAConstruction` 零扇入，**在本轮 HEAD 上已不成立**。

**诚实边界**：这些定理的**主语是 `AlphaData`（一个观测映射）**，α 只取**一条**实例 `e`，值与 `obs` 一一对应。
⟹ α 在这里是「**观测的闭包**」而不是「**学习的抽象**」。这与净版对 α 的高要求（`净版:1865` 把可计算性登记为 8.17）不完全同型。
**我仍判 ✅，因为 5.5 问的只是「与 FCA 导出算子的关系」**，那一问已被恒等地回答。

**⟳ 旧判「🟡（净版禁的是『同构』而非『关系』）」为何改为 ✅**：
旧版的顾虑是对的（净版禁同构），但它把结论方向搞反了——
**正因净版禁同构，Lean 给映射等式而不宣称同构，才恰好符合净版**；
而净版真正说「未建立」的那件事（**映射**），Lean 已经给了。

---

### 5.6 `C` 的结构 —— 🟡 部分（**旧判 ✅ 是错的**）

```
$ grep -n -e 'structure CtxSpace' -A4 Fate/Frame.lean
292:structure CtxSpace where
293-  Carrier : Type*

$ grep -rn 'CtxSpace where' Fate/ | wc -l
23

$ grep -n -e 'structure CtxParts' -A10 Fate/InstanceChain.lean
73:structure CtxParts where
75-  Local : Type u        -- 局部域
77-  U : Type u
79-  Act : Type u
81-  Θ : Type u
84:def CtxParts.Carrier (P : CtxParts) : Type u := P.Local × P.U × P.Act × P.Θ

$ grep -n -e 'def RichCtx' -A2 Fate/LawRuleToTraj.lean
411:def RichCtx (F : Frame) : CtxSpace :=
412-  ⟨F.U.Carrier × F.Ν.Carrier × F.Θ.Carrier × F.Act.Carrier⟩

$ sed -n '139,144p' Fate/WorldModelCompleteV2.lean
**⚠ 上下文的选择**：γ / ∘ / υ / `rules` 都需要一个 `CtxSpace`。
本结构**不**把 `CtxSpace` 做成字段（那会使 `F.X` 与它各指一个空间），
而是取**唯一**的 `⟨PUnit⟩ : CtxSpace`（单点上下文）。
**这是刻意的退化**：`CtxSpace` 的选取属 A9／开放问题 8.5，
本文件**不擅自假定**其内容（登记为未完成项 U4）。
```

| 具体 `C` | 位置 | 内容 | 含时间？与 `x` 的关系 |
|---|---|---|---|
| `CtxParts` | `InstanceChain.lean:73-85` | `Local × U × Act × Θ` | **不含时间**。`Local` 是状态空间的**子集类型**（`:94` `Partition X := X → Set X`），与 `x : X.Carrier` 不同层 |
| `RichCtx` | `LawRuleToTraj.lean:411` | `U × Ν × Θ × Act` | **不含时间**。让 `IsDirac` 抽出的函数「吃到」四元组（`:403-406`）；**只被 `LawRuleToTraj` 一个文件用** |
| `FormalCtx` | `FCA.lean:92` | `GFCA × MFCA × Irel` | 形式背景，非上下文 |
| `WorldModelCompleteV2` | `:139-143` | **`⟨PUnit⟩`** | **刻意退化**；登记为未完成项 **U4** |

**判定：🟡 部分。**
- 净版问「`C` 的**结构未定义**」：**「一般」结构确实仍未定义**（`CtxSpace` 只有 `Carrier`，无结构约束）。
  但**已有 4 个具体实现**，其中 `CtxParts` 已把净版 `:1771` 的两问都答了（「是否含时间」→ **否**；「与 `x` 如何区分」→ `Local` 是 `X` 的子集类型）。
- **不能判 ✅ 的原因**：主干上实际使用的 `WorldModelCompleteV2` 取 `PUnit`（单点），
  即「**上下文依赖**」在主结构里**被退化成没有上下文**。`RichCtx` 只被 1 个文件用（`grep -rln RichCtx` → `LawRuleToTraj`），
  `CtxParts` 只被 `InstanceChain` 用（同文件）。⟹ **有 4 个 C，没有一个进主结构；5.6 的实质（主链上的上下文依赖）仍未闭合。**

**⚠ 顺带发现一处登记错位（小错，非内容错）**：`WorldModelCompleteV2:140-142` 把「`CtxSpace` 的选取」挂到「开放问题 8.5」，
但 `InstanceChain.lean:33/93/98` 用的 8.5 是「**局部域如何从数据学到**」（对应净版 `:3265` 的 `X_local` 划界）。
**二者不是同一个问题**，建议更正引用。

---

### 5.7 覆盖率/准确率/简洁度 —— 🟡 部分（**旧版「语义待核实」现已核实：语义不同**）

```
$ grep -rn 'Coverage|Simplicity|Accuracy|准确率|覆盖率|简洁' Fate/ --include=*.lean
Fate/AlphaStatistical.lean:320:def Coverage (B : Band Y) (S : Sample C X Y ι)
Fate/AlphaStatistical.lean:585:    LawRule.IsPoint (statAlpha B S s) ↔ Coverage B S s
Fate/ICPCoverage.lean:109:theorem icp_coverage
（其余「简洁」命中均为工程文档修辞，如 `Completeness.lean:422`）

$ sed -n '315,322p' Fate/AlphaStatistical.lean
/-- **（C）覆盖条件**：每个格位都不低于最小样本量。
$$(C)\ :\ \forall c\,x,\ n(c,x)\ge n_{\min}.$$
**这是统计条件**：它说「**没有**一个格位是没样本的」。 -/
320:def Coverage ... : Prop := ∀ c x, S.count s c x ≥ B.nMin
```

| 净版要的量 | Lean 里有无 | 说明 |
|---|---|---|
| **覆盖率** | 🟡 **两个，都不是净版要的** | ① `AlphaStatistical.Coverage`(`:320`) = **采样覆盖**（`n(c,x) ≥ n_min`），配 `IsPoint ⟺ Coverage ∧ BandCollapse`(`:585`)；② `ICPCoverage.icp_coverage`(`:109`) = **ICP 预测集包含真因果父集的概率下界**（显式化论文隐藏前件 `Prob.compl_add` `:84`）。**净版要的是「规则覆盖了多少数据/状态」的比率** |
| **准确率** | ❌ **零命中** | 只有**间接**的：`ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification`(`:221`) 给「分类正确」的**充分条件**（`sgn (s+δ)=sgn s`），**不是准确率公式** |
| **简洁度** | ❌ **零命中** | 「简洁」命中全是修辞 |

**判定：🟡 部分（1/3 且非同一量）。** 严格说，5.7 的**实质（规则质量的度量）在 Lean 里仍未实现**；
判 🟡 只因「覆盖率」这个词有一个真定理（`icp_coverage`）背着。
**这正是任务书要求「区分真的实现了与名字像」的典型：必须写明它答的不是净版那一问。**

---

### 6.10 效应估计只给组平均 —— ⚠ 净版已过时（**含一条降级说明**）

**实测**：

```
$ grep -rn 'CATE' Fate/
（零命中）
$ grep -rn 'treatment|Treatment' Fate/
（零命中）
$ grep -rln 'CATE|cate|individualTreatment|IndividualEffect|heterogen' Fate/
Fate/UpsilonOperator.lean  Fate/LawRulePointDecidability.lean  Fate/WorldModel.lean
Fate/LawRulePointDecidability.verified.lean  Fate/ConvergeToOptimalDemo.lean
Fate/ViewOneCounterfactual.lean
（上述命中均为**子串误匹配**：`CATE` 出现在 `DERIVATIVE`/`INDICATE`/`LOCATE` 等词中，非概念命中）
$ grep -n '效应' Fate/Frontdoor.lean
107:**⟹ 任务所说的「退化为 backdoor」只在「`Z` 单点且 `X` 无效应」的平凡情形下成立；
142:**故「退化」成立的分界点是「`X` 对 `Y` 无因果效应」**。
（修辞用法，非「效应量估计」）
```

**已有但**不同**的实现**：

| 模块 | 它做了什么 | 为什么**不是** 6.10 的答案 |
|---|---|---|
| `TieredScheme`（§29 分档） | 「**粗档单值 ⟹ 细档单值，其逆不成立**」；三档 = 预测 `~obs` / 干预 `~int` / 反事实 `~cf` | 它说的是**识别粗细的蕴含**，不是「组平均 ⟹ 个体」的**不可推性** |
| `CfPartialIdent`（48 定理） | `u` 不可观测 ⟹ 反事实**只能部分识别**，给 `cfIdentSet` 区间 + 点识别充要条件（`pointIdent_iff_lower_eq_upper` `:322`）→ **个体层** | 是**个体层的区间**（不是组平均），且是**认识论不确定性** |
| `ErrorCriterionImpliesBound:221` | **单实例**分类正确（`sgn : ℝ → ℤ`，`ErrorBound.lean:104`）→ **个体粒度** | 那是**分类**不是**效应量** |
| `CounterfactualStrictness.cf_strictly_weaker_than_eq` | 「反事实等价**严格弱于**相等」 | 不是「组 ⟹ 个体」 |

**判定：⚠ 净版已过时（所担心的对象在 Lean 里不存在）。**

理由：
1. 净版 6.10 的前提是「效应估计的结论是**组平均水平**」——这是关于**原素材的估计量**的陈述。
2. **Lean 里 `ATE`/`CATE`/`ITE`/`treatment` 作为概念全部零命中** ⟹ Lean **从未实现过「组平均效应估计」**。
3. 因此「个体命运不能由组平均推出」这条禁令，在 Lean 里**既没被违反，也没被证明**——它**没有对象可指**。
4. 而**个体层的东西是有的**（`CfPartialIdent` 的区间、`sgn` 的单实例分类、`TieredScheme` 的档间蕴含），
   只是它们**不走「组平均」这条路**。

**⚠ 本条判定的可信度必须降级（阴性证据）**：
判「⚠ 净版已过时」**基于「零命中」**。阴性证据弱于阳性证据：
若作者所说的「效应估计」指**别的名字的模块**（我按 `CATE`/`ATE`/`treatment`/`效应`/`individualTreatment` 五组词搜过），
本条会错。**建议主控复核：是否真有被称作「效应估计」的 Lean 模块。**
**另**：净版 6.10 作为**理论文档的告诫**（禁止用 ATE 说个体命运）**仍然合理**；
只是它作为「**Lean 里待核查的问题**」**已失去所指**。

---

## 四、最值得立刻写进文档的（按价值排序）

| 排序 | 开放问题 | 为什么重要 | 建议 |
|---|---|---|---|
| **1** | **5.5 FCA 导出算子与 α** | 净版说「**关系未建立**、『形式相似』不得写作同构」；Lean 里是**恒等 + Galois + hexagon + 可算性**，**且已被 `WorldModelCompleteV2.alpha` 用作字段类型**。**这是「作者说已经实现掉了」的最强例证**，直接推翻净版一条负面判断 | 净版 5.5 处标注「**Lean 已实现（端到端）**」，指向 `AlphaFCAConstruction.lean`（`:121/:129/:168/:358/:384`）+ `AlphaAndStochasticWiring.lean`（`:235/:249/:254/:259`）。**同时保留净版的「不得写作同构」禁令**——Lean 未越线，正好互相印证 |
| **2** | **1.2 `F_traj` 的可测性** | **存在一个逐字引用净版 `:158` 专为此问题写的模块**，且已证 2 条可测性定理。净版「本章均未给出」在 Lean 侧**已不成立**。这是「**你得找出来写文档**」的字面证据 | 净版 1.2 处加注：「**Lean 侧有部分答案**：`Fate/TrajGenMeasurable.lean`（`trajGen_measurable_at` `:138` / `trajGen_measurable` `:181`），条件是 5 条 `MeasurableSpace` + 单步 `f` 联合可测；**`θ`、`x₀` 作为定义域部分未做**」 |
| **3** | **2.3 「慢」的阈值** | **净版把 2.3 当核心开放问题，但作者裁决 Q-1 已废除「阈值判据」整条路线**。净版 2.3 的**前提已被推翻**，文档必须改，否则它会继续被当成「待解阻塞」 | 净版 2.3 处写：「**本条已因作者裁决 Q-1 失效**：`ε=τ_fast/τ_slow` 判据被废除（`Frame.lean:596-600`），代之以『θ 在提取样本上稳定』（`:626`）+ 定量版（`ThetaStabilityMetric.lean:50`）。**⚠ 净版的 `ε₀`（时间尺度）与 Lean 的 `ε`（参数距离）不是同一个量**」 |
| **4** | **5.3 `∼_E` 的判据** | 净版说「判据未给 ⟹ 阻塞定义 5.13 的可计算化」。Lean 有**两条内生判据**，第二条是**作者授权 Q-3 的正式消解**（文件头明写「悬置 → ✅ 消解」） | 净版 5.3 处标注「**已实现（两套）**」，指向 `InstanceChain.AlphaSpec`(`:216-259`，判据 = `partition_eq_iff`) 与 `AlphaKernel.alphaKernel`(`:58`)。**注明二者互不推出（未核实是否有桥）** |
| **5** | **5.6 `C` 的结构** | **旧版判「✅ 已实现（`Frame:292`）」是错的**，会误导后续工作。真实状态是「4 个具体 C，但主结构用 `PUnit`」 | 净版 5.6 处写：「`CtxSpace` 只是 `Carrier : Type*`（无结构约束）；**4 个具体实现**：`CtxParts`(`InstanceChain:73`)、`RichCtx`(`LawRuleToTraj:411`)、`FormalCtx`(`FCA:92`)、`TieredScheme`；**主干 `WorldModelCompleteV2` 取 `⟨PUnit⟩`（刻意退化，登记 U4）**⟹ 主链上下文依赖**未闭合**」。**并更正 `WorldModelCompleteV2:140-142` 把 5.6 挂「8.5」的引用错位** |
| **6** | **2.1 `u_t` vs `ε_t`** | **最干净的 ✅**。净版说「从未区分」，Lean 侧**完全不成立** | 净版 2.1 处标注「**已实现**（类型层强制不可互换，`Frame.lean:79/83/150`；`trajLaw` 里 u 保持序列、ε 变分布）」，注明「`u_t` 是否也是随机变量」这一半**取了确定性约定**而非证明 |
| **7** | **2.2 `a_t` 与 `u_t` 分解** | **核查期间刚入链**（`6b6d0f4`），有**具体反例 + 充要条件**。净版「未给」现已有一大块 | 净版 2.2 处标注「**第一问已答（否 + 充要条件：带左逆单射 `Act → U`）**，见 `ActInputDecomp.exists_decomp_iff`(`:283`)；**第二问（取值空间独立性）未答**」。**⚠ 不要照抄 commit message 的「完整回答」，那是夸大** |
| **8** | **5.4 编码算子 + 误差界** | 净版是**合取**式，必须拆开写，否则会被误读为「已完成」或「完全未做」 | 净版 5.4 处拆两半：「`enc` 存在性 + 自洽性 **已实现**（`Alpha.lean:111/134`）」/「**误差界未实现**（`Alpha.lean:110` 自述、`LabelAudit:1329` 复核）⟹ **『FCA 不得进主链』这条后果在 Lean 里仍无依据**」 |
| **9** | **1.3 因果事件与 `x_t`** | **最容易被写成「已实现」而实际是「换了读法」** | 净版 1.3 处写：「**『因果事件 `e_i`』这个对象在 Lean 里不存在**（`CausalEvent` 零命中）；但『`e_i` = 转移 `f` 的一次施加』已由 `SCMWorldModel.scmWorldModel_sim_succ`(`:408`) 落地。**宏观反馈条件概率（已知 1.3）无处对应**」 |
| **10** | **5.2 结构性指标** | **旧判「✅（5 模块）」过宽**，会掩盖真缺口 | 净版 5.2 处写：「**稳定性有（θ 的）：`ThetaStableOn`/`ThetaStableWithin`**；唯一性只在局部域划分与 σ 上有；**可恢复性无**。且三者**均不是「规则质量度量」**——净版 5.2 的主语（规则）上仍全缺」 |
| **11** | **2.4 命显／命隐** | 净版自己已废（`:25`「已删除且不得回流」），继续列为「开放问题」会**虚增数** | **从「活跃开放问题」清单移出**，改为「**条件性登记**：仅在恢复四象限表时适用（`净版:730`）」 |
| **12** | **6.10 / 5.7 / 1.1 各一句** | 三条都有「名字像」陷阱 | **6.10**：「ATE/CATE/treatment 全库零命中 ⟹ 净版担心的『组平均』对象不存在；本条**有理论价值、无 Lean 对应物**」（**标注为阴性证据**）。**5.7**：「覆盖率有 `icp_coverage`，**但它答的是 ICP 覆盖率不是规则覆盖率**；准确率/简洁度零实现」。**1.1**：「`trajLaw` 已存在（`TrajGenStochastic:201`）；`ℕ`/`ℝ≥0` 缺；**`trajLaw` 类型未带 `IsProbabilityMeasure`**（两文件 `grep -c` 均 0）」 |
| — | **1.4 / 1.5** | 直说 | 文档中**直说「❌ 未实现」**，不要写「部分」。 |

---

## 五、诚实边界

### 5.1 已核实（本报告每条结论的证据类型）

| 陈述 | 证据 |
|---|---|
| 构建成功 9275 jobs | `lake build Fate` → `Build completed successfully (9275 jobs).` EXIT=0（本轮实测） |
| HEAD 从 `f3b9083` 推进到 `6b6d0f4` | `git log --oneline -3` 两次，间隔约 1 小时 |
| 677 / 620 / 604 / 7689 | `python3 -c`（`os.walk` / `os.listdir`）、`grep -c`、`python3` 逐文件正则 |
| `CausalEvent`/`PathDep`/`ATE`/`CATE`/`treatment`/`Recoverab`/`Accuracy`/`Simplicity` 零命中 | 逐个 `grep -rn` 实测，输出已贴 |
| 2.1 的类型分离 | `sed -n '73,83p'`、`'110,111p'`、`'147,151p' Fate/Frame.lean` 逐字 |
| 1.2 的模块内容与「不声称已解决」 | `head -90 Fate/TrajGenMeasurable.lean` 逐字 + `grep OutputSeq` |
| 5.5 的恒等链条与净版禁令原文 | `grep -n -e 'polarUp_eq' ...` + `sed -n '344,345p;358,360p'` + **`净版:2105` 全文实核** |
| 2.2 的 11 条定理与新入链 | `git log` + `grep -n -e '^theorem' Fate/ActInputDecomp.lean` + `sed -n '300,340p'` 逐字 |
| 2.3 的 Q-1 裁决文本 | `sed -n '583,604p'`、`'608,628p' Fate/Frame.lean` 逐字 |
| 5.4 的「误差有界未做」 | `Fate/Alpha.lean:105-110` 逐字 + `Stage0/LabelAudit.lean:1329` |
| 5.6 的 `CtxSpace : Carrier : Type*` 与 4 个具体实现 | `grep -n -e 'structure CtxSpace' -A4`、`grep -rn 'CtxSpace where' \| wc -l` → 23、`CtxParts`/`RichCtx` 逐字 |
| 5.3 的两套判据 | `sed -n '216,232p' Fate/InstanceChain.lean`、`sed -n '58,66p'` + 文件头 `:60-64` `Fate/AlphaKernel.lean` |
| 1.1 的 `trajLaw` 与 `iidMeasure` | `grep -n 'def trajLaw' -A8`、`grep -n 'def iidMeasure' -A2 Fate/SigmaEstimation.lean` 逐字 |
| `IsProbabilityMeasure` 零命中 | `grep -c -e IsProbabilityMeasure` → `TrajGenStochastic:0`、`AlphaAndStochasticWiring:0` |

### 5.2 方法性风险（必须由主控知情）

| # | 风险 | 说明 |
|---|---|---|
| **1** | **阴性证据的说服力** | 6.10、1.4、1.5、5.7 的「零命中」类结论**依赖搜索词选对**。我用了中英双轨（`CATE\|treatment\|ATE` / `效应`；`PathDepend\|MultiStable\|Memory`；`Simplicity\|Accuracy` / `准确率\|简洁`）；若作者用其它词（如「处理效应」「轨迹依赖」），可能漏。**这三条请复核** |
| **2** | **SSH 包装层吞 `$` 与双引号** | `run.js` 的 `argv.join(' ')` 使 `$` 展开、双引号剥离。**一次误用 `grep -rl "import Fate.WorldModel$"` 的输出已作废**，未进入任何结论。本报告全部取证改用 `-e PATTERN` + `python3` 构造 |
| **3** | **扇入数字一律未使用** | 本轮**没有重跑** `fanin_check.py`（C6/F1 的扇入是第 376/428 轮快照）。F1 说 `AlphaFCAConstruction` 零扇入，我在 HEAD 上按名字实测它**有**消费者（`AlphaAndStochasticWiring` 10 条 + `WorldModelCompleteV2:164` 字段类型）——但这是**按名字 grep**，不是扇入算法口径 |
| **4** | **`ActInputDecomp` 是核查中途出现的** | 它属 `HEAD 6b6d0f4`，我多数核查在 `f3b9083` 上做。**若主控基线是 `f3b9083`，则 2.2 应回到 ❌**。请以「卷上当前状态」为准 |
| **5** | **判定反复的历史** | 2.2/5.2/5.5/5.6 在本项目历史上被判过不同结论（见 §2.2）。**本轮的改判都附了理由**；若主控认为某次改判不当，应据 §2.2 的表回溯 |

### 5.3 未核实（明确列出）

| # | 项 | 为什么未核实 |
|---|---|---|
| 1 | **`trajLaw` 是否为概率测度** | 只确认 `IsProbabilityMeasure` 在 `TrajGenStochastic.lean` 与 `AlphaAndStochasticWiring.lean` **零命中**；**没有**全库搜第三处是否有证明 ⟹ 「路径上的**概率**测度」这一点**未核实** |
| 2 | **5.3 两套判据（`AlphaSpec` 划分 vs `alphaKernel` 核）是否有桥** | `grep` 未找到「α 的核 = 局部域划分」的定理；**未核实是否有**，也可能需要一条桥定理才成立 |
| 3 | **1.2 的「定义域 σ-代数」是否只有 `TrajGenMeasurable` 一个答案** | 我搜了 `InputSeq` 与 `Measurable`，**未穷举**全库所有「轨迹可测性」写法 |
| 4 | **2.4 的四象限表在 Lean 里是否曾有过实现** | `Manifest`/`Hidden` 零命中，但历史实现若存在可能已被移入 `_archive_superseded/`，**未查** |
| 5 | **6.10 的「效应估计」是否有别的名字** | 见 §5.2 风险 1 |
| 6 | **净版「14 显式 + 3 表格 = 17」的计数来源** | 净版实际编号开放问题共 **26 条**（第 1 章 5 + 第 2 章 4 + 第 3 章 3 + 第 4 章 2 + 第 5 章 7 + 第 6 章 12 + 第 7 章 2 + 第 8 章 22；`净版:3297` 的「合计：22 条」仅指第 8 章）。**任务书的 17 与本核查覆盖的 16（除去 5.1）口径不同，未核实 17 是怎么数出来的** |
| 7 | **`_archive_superseded/` 与 `_quarantine/` 内容** | 本轮**完全未查**（任务范围是 `Fate/`） |
| 8 | **`Fate/Stage0/`、`Fate/Stage2/`、`Fate/scratch/` 是否在链上** | 我只对 `Fate/*.lean`（620）与 `Fate.lean` 的 604 条 import 做统计；子目录不在 `os.listdir('Fate/')` 里，**未统计其入链情况** |
| 9 | **旧版 §五.6 的「未读第 8 章附录 B.3」** | 本轮**仍未读**附录 B.3（`净版:3379` 引了它），故「命显/命隐是否真的完全不出现」**未核实**。我核了 `净版:25`、`:730`、`:3379` 三处 |

### 5.4 本报告**不做**的判断

1. **不判断「净版该不该改」**。本报告只给「Lean 里有没有」；「净版怎么写」是 §四的**建议**，不是结论。
2. **不判断「哪些结论是虚报」**。`ActInputDecomp` 的 commit message 写「完整回答」，我指出它只答了一问——但**不判断**这是有意夸大还是措辞宽松。
3. **不修改任何 `.lean`、不修改任何既有 `.md`**（除本文件）。
4. **不把「零 sorry」当「正确」**。本轮未跑 `sorry`/`axiom` 扫描；构建成功（9275 jobs）**不排除** `sorry`。

---

## 附：本次核查所用命令（可复现）

```bash
# 基线
cd /root/fate-dev
git rev-parse --short HEAD                    # f3b9083 → 6b6d0f4（核查中途前进）
ls Fate/*.lean | wc -l                        # 620
grep -c -e "import Fate\." Fate.lean          # 604
export PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
lake build Fate 2>&1 | tail -3                # Build completed successfully (9275 jobs).

# 定理数（逐文件；python3 用 chr() 构造正则，因 SSH 包装层吞 $ 与引号）
python3 -c 'import os,re; d=chr(70)+chr(97)+chr(116)+chr(101)+chr(47); ...'   # 7689

# 零命中类（逐条）
grep -rn -e 'CausalEvent' -e 'causalEvent' Fate/
grep -rn -e 'PathDep' Fate/
grep -rn -e 'CATE' Fate/
grep -rn -e 'treatment' Fate/
grep -rn -e 'Recoverab' Fate/
grep -rn -e 'Manifest' -e 'Hidden' Fate/*.lean

# 关键证据
grep -n -e 'def trajLaw' -A8 Fate/TrajGenStochastic.lean
head -90 Fate/TrajGenMeasurable.lean
sed -n '73,83p;110,111p;147,151p;292,294p;583,604p;608,628p' Fate/Frame.lean
grep -n -e '^theorem' -e '^def' -e '^structure' Fate/ActInputDecomp.lean
sed -n '300,340p' Fate/ActInputDecomp.lean
grep -n -e 'polarUp_eq' -e 'polarDown_eq' -e 'takeConcept_eq_closureOp' Fate/AlphaFCAConstruction.lean
sed -n '344,345p;355,400p' Fate/AlphaFCAConstruction.lean
sed -n '216,232p;235,262p' Fate/InstanceChain.lean
sed -n '55,70p' Fate/AlphaKernel.lean
sed -n '105,140p' Fate/Alpha.lean
sed -n '315,325p' Fate/AlphaStatistical.lean
sed -n '50,60p' Fate/ThetaStabilityMetric.lean
sed -n '135,145p' Fate/WorldModelCompleteV2.lean
grep -n -e '^theorem' Fate/AlphaAndStochasticWiring.lean
```

**核查环境**：`node C:\Users\xingg\Desktop\服务器\.sshnode\run.js ct.hylab.im <cmd>`，非交互 shell；
`lake` 需给全字面量 PATH 前缀（`export PATH=/root/.elan/bin:/usr/local/sbin:...`，因 `$` 会被吞）。
