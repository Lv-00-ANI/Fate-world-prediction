# Mathlib 缺口与自建库范围（依实测调研重写版）
---

> ## ⚠️ 第 380 轮作者修正（2026-10-23）— 全文「旁路」表述已被推翻
>
> **作者原话（第 376 轮对话）**：
> > 「**因果不是旁路啊  没有任何东西是旁路只要可以达到目标**」
>
> **⟹ 本文件中一切把因果层称为「旁路」/「可选层」/「可绕过」的表述，其「可选/可绕过」的部分作废。**
>
> **作废的论证依据**（原文遗留在下方，仅供追溯，**不得据以行事**）：
> - `06-矛盾裁决表.md` 第 5 条「因果作为可接入的中间机制置于旁路」
> - `00-作者裁决A-B.md`「因果不再是规则的上游，而是旁路/可选层」
> - 任何「实例 → 规则 → 预测」为唯一主线、因果旁置的架构图
>
> **现行口径**：因果层是**主干的一部分**。与裁决 O（因果进入分类循环）方向一致。
> 因果在架构中的精确位置，见 `_audit/C3-裁决总汇总-第376轮.md` §一 与 §五（主干断点 B1：因果⇄分类全断）。
>
> **本标注遵循项目「不静默删除」纪律：原文一律保留，只在文首加此标注。**

---

> **本文件地位**：`proof-engineering/` 数学证明路线的产出物之二，对应 `00-总纲.md` 第四节产出物清单中的 `02-Mathlib缺口.md`。
>
> **本文件的写作性质**：本文件是**重写**，不是修订。其原因是：本文件的上一版对 Mathlib 与 Lean 生态现状的全部判断均基于「既有知识、未联网、未本地核对」，而**后续调研在联网与本地实测条件下推翻了其中多处**（最重大的一处：上一版称随机分析须自建，实测布朗运动已在 Mathlib 主线）。旧版本的错误清单与逐条修正见第十节。
>
> **上游约束**：
> - [`00-总纲.md`](00-总纲.md) 第三节（「原则上可形式化」与「现有覆盖」两栏必须分开）；
> - [`../03-规范与裁决/01-作者裁决C-最彻底.md`](../03-规范与裁决/01-作者裁决C-最彻底.md)（**裁决 C：最彻底原则；裁决 D：$\alpha$ 具体化为 FCA 取概念过程；裁决 E：主量纲＝决策损失；裁决 F：A33/A34 正式加入**）；
> - [`../03-规范与裁决/02-作者裁决G-依赖规程.md`](../03-规范与裁决/02-作者裁决G-依赖规程.md)（**外部依赖处理规程：用但要检查，每依赖单独建档，逐条对抗性审查，一切能复用就复用**）；
> - [`../03-规范与裁决/03-作者裁决H-lattice搁置.md`](../03-规范与裁决/03-作者裁决H-lattice搁置.md)（**FCA 暂缓：`level0000x/lattice` 先当没有，待作者整理**）。
>
> **证据政策（本文件的核心纪律）**：本文件对现状的**每一条判断**都必须标注证据来源与强度。四种标注的含义固定如下：
>
> | 标注 | 含义 | 可作何用 |
> |---|---|---|
> | `[实测文档页]` | 本次写作中**直接抓取官方文档页并读到签名/正文**（HTTP 200），或尝试抓取而得到 404 | **可作成本论证的硬依据** |
> | `[实测仓库文件]` | 直接读取仓库的 `lean-toolchain` / `lakefile` / 源文件 / 声明清单 | **可作硬依据**（但注意其时效性） |
> | `[调研代理报告]` | 来自 `ref/` 下的调研文档，该文档自述的调研方式与凭证 | **可作线索与论证依据，不可单独作为硬依据** |
> | `[需进一步核实]` | 未查到、或查到但无法以可核验方式确认 | **不得作为任何工作量安排的依据** |
>
> **一条贯穿全文的诚实边界（采纳自对抗审查）**：凡**未跑 `lake build`** 的，「0 命中」一律读作「**在已搜索的记号空间内未发现**」，**不得读作「确定不存在」**。这一条适用于本文件引用的**全部**外部库覆盖度判定。
>
> **成本口径（依裁决 C 第四节第 4 条）**：规模估计**一律用五档相对量级**（胶水代码／小项目／中等项目／大项目／研究级），**不给任何年数**，且**逐项标注依据来源**。
>
> **本机环境（已实测）**：`lean`、`lake`、`elan` 均已安装；已装工具链为 `leanprover/lean4:v4.14.0`（默认）与 `leanprover/lean4:v4.33.0-rc1`。**即：本路线具备本地构建验证能力**——这是把本文件中一切「假设」变为「事实」的唯一途径。

---

## 一、两栏原则（保留并强化为三栏）

### 1.1 两栏各自回答什么

形式化路线上的每一个数学对象，都必须同时接受**两次独立提问**：

- **第一栏「原则上可形式化」**问的是：*这个对象能否被写成 Lean4 中的类型与命题？* 这是一个**数学与逻辑**问题。它的答案几乎总是「是」——因为 Lean4 基于依值类型论，数学上被清楚表述的对象原则上都能翻译为类型，被清楚表述的命题原则上都能翻译为 `Prop`。这一栏的否定答案极为罕见，且必须有**逻辑上的理由**（例如该陈述包含自指悖论、或其所用概念在数学上尚未被定义清楚）。
- **第二栏「实际覆盖」**问的是：*在我写下这个定义之后，现成的东西里已经有多少可以直接拿来用？* 这是一个**工程事实**问题，其答案依赖于**具体仓库当前的内容、版本与选题取向**，因而**会随时间变化**，且**可能与任何人的既有判断不符**。

两栏的答案类型不同、变化速率不同、承担的功能也不同。第一栏的答案决定了「这件事是否值得做」，第二栏的答案决定了「这件事要花多少力气、从哪里开始做」。

### 1.2 本文件新增的第三栏及其必要性

上一版只有两栏。**两栏在实测之后被证明仍然不足以支撑工作量判断**——因为「实际覆盖」这一栏本身必须区分「Mathlib 主线覆盖」与「上游生态覆盖」：

> **一个对象可以既不在 Mathlib 中，又完全不必自建。** 因果推断（SCM、do 算子、do-calculus、识别、部分识别）不在 Mathlib，这一事实在旧版中被正确地指出，但旧版由此推出的结论——「必须自建 `Causality.*` 全族」——**被后续的实测推翻**：Causalean（现名 CausalSmith）已经提供了这一族的高质量实现。
>
> **因此，本文件的现状核查表强制分为三栏**：原则上可形式化 ／ Mathlib 实际覆盖 ／ **现成库（含链接与证据）**。第三栏的取值决定「是自建还是复用」，第二栏的取值只决定「复用时的底层可借多少」。

### 1.3 混栏为什么会产生严重误读（保留旧版分析）

**混栏的第一种后果：把「可做」读成「好做」。** 若把两栏合并为一栏并写「Mathlib 能处理 SCM」，读者会得到「SCM 已有基础、只需适配」的印象；而真实情况是：SCM 的定义需要从零写起，Mathlib 不提供任何现成构件。这一个字的差别，直接改变了工作量级的判断——从「胶水代码」变成了「从零建一个库」。

**混栏的第二种后果：同一对象在两处得到互相矛盾的标注。** 原文第 23 轮即出现了这一现象，可逐字比对：

- 该轮第一张表（`（过程产物，不在成品集内）`）在「SCM 定义、干预定义」一行，于「能否 Lean4 形式化」列填「能」，于「现状」列填「可形式化」；
- 该轮第三张表（同文件 `:1644–1646`）在「没有的」清单中，列出了「SCM 的形式化」「do-calculus 的形式化」「反事实的形式化」。

同一轮对话内，SCM 既在「能形式化」一表中，又在「没有的」一表中，**两处措辞不冲突但读者会读出冲突**：前者说的是第一栏（原则上可做），后者说的是第二栏（当时视野内没有）。原文把两栏塞进同一列导致这一现象，并且**从未声明两栏的区别**。其后果不是「读者可能误解」，而是**该表无法承担工作量估计这一功能**——因为工作量恰恰由第二栏与第三栏共同决定，而这两栏在原文的表里都没有被独立地写出来。

**混栏的第三种后果：掩盖「缺口不会被上游补上」这一事实。**

> **Mathlib 缺因果推断，不是「正在补的坑」，而是「不在其选题范围内」。**

Mathlib 的选题取向以**代数、数论、分析、测度论、拓扑、范畴论、组合**等经典数学分支为核心。结构因果模型、do 算子、后门／前门准则、do-calculus、反事实语义——这些对象的主体在**统计学、计量经济学与人工智能**的文献传统内。因此这不是「等一年就有人写好」的情形。这一判断**至今未被推翻**，反而被实测加强：治理这一缺口的不是 Mathlib，而是**一个独立的第三方库**（Causalean），而该库是**由一条自主流水线持续增长的**，不是 Mathlib 的一部分。

**混栏的第四种后果（本次实测新增）：把「不在 Mathlib」误读为「必须自建」。** 这是旧版最实质的错误。旧版在第二节把「布朗运动」「鞅收敛」「ODE」「统计学习理论」「Lyapunov」逐项标为「部分有／不确定／无」，并据此把它们全部或部分划入自建范围。实测结果见第二节：其中**五项其实已经有可直接复用的现成实现**，只是不在 Mathlib 里。**「Mathlib 没有」是一个关于 Mathlib 的事实，不是关于世界的事实。**

**结论（本文件的执行规则）**：下文第二节的表格**强制分成三栏**，任何一行不得少于三栏。第二栏的取值只有四种：**有（直接可用）／部分（有周边构件，核心需补）／无（Mathlib 中无）／不确定**。第三栏的取值只有五种：**★ 可直接用 ／ ◆ 需适配 ／ ▲ 仅参考 ／ ✖ 无现成项目 ／ ⏸ 暂缓**。

---

## 二、现状核查表（全部重做）

**表头说明**：本节逐项给出**三栏**，另加「实测依据」与「证据强度」两列。**凡证据强度为 `[调研代理报告]` 或 `[需进一步核实]` 者，不得作为工作量安排的硬依据。**

**关于 Mathlib 覆盖栏的版本口径**：本表第二栏的 `[实测文档页]` 判定，其抓取时 Mathlib 官方文档站所服务的源 commit 为 `9e6b3aac99b624d10c84653ab9c5357283b9b3b8`（该 hash 出现在抓取到的源码链接中）。**该 commit 不等于 Mathlib master 的当前 HEAD**，故第二栏的「有／无」是**该 commit 时点的事实**。

| 数学对象 | 原则上可形式化 | Mathlib 实际覆盖 | 现成库（含链接） | 实测依据 | 证据强度 |
|---|---|---|---|---|---|
| **测度论** | 是 | **有** | Mathlib 主线 | `MeasureTheory` 为 Mathlib 成熟大块（测度、外测度、Bochner/Lebesgue 积分、乘积测度、符号测度、Radon–Nikodym）。本次未逐模块抓取，属既有覆盖的常识性事实 | `[调研代理报告]` |
| **概率论基础** | 是 | **有** | Mathlib 主线 | `ProbabilityTheory`：概率空间、随机变量、期望、方差、独立性、条件期望、`CondIndepFun`、`Kernel`。本次抓取的 ODE/布朗运动/鞅三个文档页的 import 链侧面印证了 `MeasureTheory.Function.ConditionalExpectation`、`MeasureTheory.Function.UniformIntegrable`、`Probability.Process.Filtration` 等模块的**存在** | `[实测文档页]`（间接，限上述模块名） |
| **鞅（定义、停时、上鞅／下鞅）** | 是 | **有** | Mathlib 主线 | 抓取 `Mathlib.Probability.Martingale.Convergence` 文档页（HTTP 200），正文出现 `MeasureTheory.Submartingale`、`MeasureTheory.Martingale`、`Filtration`、`UniformIntegrable` 等类型与 `MeasureTheory.uniformIntegrable_iff` | `[实测文档页]` |
| **鞅收敛（Doob）** | 是 | **✅ 有**（旧版标「不确定」——**已推翻**） | Mathlib 主线 | `Mathlib.Probability.Martingale.Convergence` 文档页逐字给出：`MeasureTheory.Submartingale.ae_tendsto_limitProcess`（**a.e. 鞅收敛定理：L¹ 有界下鞅几乎处处收敛到其 `limitProcess`**）；`Submartingale.tendsto_eLpNorm_one_limitProcess`（**L¹ 鞅收敛定理 part a**）；`Martingale.ae_eq_condExp_limitProcess`（part b）；`Integrable.tendsto_ae_condExp` 与 `Integrable.tendsto_eLpNorm_condExp`（part c，Lévy 上升定理）。**该模块同时给出 `Filtration.limitProcess`，且其设计使「存在性」表述直接由 `limitProcess` 给出** | `[实测文档页]` |
| **布朗运动** | 是 | **✅ 有**（旧版标「部分有＋不确定」——**已推翻**） | Mathlib 主线 | 抓取 `Mathlib.Probability.BrownianMotion.Basic` 文档页（HTTP 200），逐字确认两个**主定义**：`ProbabilityTheory.IsPreBrownianReal X P`（有限维分布为布朗运动定律，即 `BrownianReal.projectiveFamily`）与 `ProbabilityTheory.IsBrownianReal X P`（前者 + **almost-surely continuous paths**，含字段 `cont : ∀ᵐ ω ∂P, Continuous fun x => X x ω`）。**主定理**：`IsGaussianProcess.isPreBrownianReal_of_covariance`（中心 Gauss 过程 + 协方差 `min s t` ⟹ 前布朗）、`HasIndepIncrements.isPreBrownianReal_of_hasLaw`、`IsPreBrownianReal.hasIndepIncrements`（**独立增量**）、`IsPreBrownianReal.indepFun_shift`（**弱 Markov 性**）、`covariance_eval`（$= \min s t$）、`IsPreBrownianReal.smul`／`inv`（**尺度不变与反演不变**）、`IsBrownianReal.tendsto_nhds_zero`。**该文档页顶部的 import 链显示 `Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily` 与 `...Distributions.Gaussian.IsGaussianProcess.*` 均为独立模块** | `[实测文档页]` |
| **Itô 积分 / 随机积分** | 是 | **✖ 无** | **`RemyDegenne/brownian-motion`（进行中）** <https://github.com/RemyDegenne/brownian-motion> ｜ blueprint §15：<https://remydegenne.github.io/brownian-motion/sect0009.html> | **实测 404**：抓取 `Mathlib/Probability/BrownianMotion/ItoIntegral.html` 返回 **HTTP 404**，确认 Mathlib **无** Itô 积分模块。上游仓库 README 逐字：「We are now building the necessary theory to define the integral against a semi-martingale, with the goal to then prove Ito's lemma.」——**进行中，未完成，未进 Mathlib**。另有论文《A Machine-Checked Itô Calculus for Brownian Motion》[arXiv:2606.15089](https://arxiv.org/html/2606.15089v2) 称机器检验了 $\mathrm{L}^2$ 积分与 $C^3$ 函数的 Itô 公式，**但该工作与 Degenne 项目的关系未核实，其仓库位置亦未定位** | `[实测文档页]`（Mathlib 无）＋ `[调研代理报告]`（上游项目状态） |
| **SDE 强解存在唯一性** | 是 | **不确定（须实测）** | **未查到任何 Lean4 形式化** | 缺口复用调研第五节「未能确认的项」第 6 条逐字：「Lean 4 中 SDE 的存在唯一性定理形式化 —— 未查到」。**该条为「未查到」，不是「确认不存在」** | `[需进一步核实]` |
| **ODE 基础（Picard–Lindelöf）** | 是 | **✅ 有**（旧版标「部分有」——**低估**） | Mathlib 主线 | 缺口复用调研记录了 `Mathlib.Analysis.ODE.PicardLindelof` 的文档页（该文档站为第三方镜像 `math.iisc.ac.in/~gadgil/PfsProgs25doc/`）。本次**未独立抓取该镜像** | `[调研代理报告]` |
| **Grönwall 不等式** | 是 | **✅ 有** | Mathlib 主线 | 抓取 `Mathlib.Analysis.ODE.Gronwall`（HTTP 200），逐字确认：`gronwallBound`（显式界，含 `K = 0` 与 `K ≠ 0` 两支）；**`norm_le_gronwallBound_of_norm_deriv_right_le`（主技术结果）**；**`dist_le_of_approx_trajectories_ODE`（两个近似解距离 ≤ `gronwallBound δ K (εf + εg) (t - a)`）**；`dist_le_of_trajectories_ODE`（两个精确解距离 ≤ `δ * exp (K * (t - a))`）；另有 `_of_mem` 变体。该页**同时注明一处 TODO**（对 `‖f' x‖ ≤ K x * ‖f x‖ + ε` 的一般化尚未做），并标明其依据文献为 Hubbard–West。**其中 `dist_le_of_approx_trajectories_ODE` 正是数值方法离散化误差分析的核心工具，且已在 Mathlib** | `[实测文档页]` |
| **Lyapunov 稳定性** | 是 | **无**（Mathlib） | **Doll & Shames《Foundations of Machine-Checked Control Theory in Lean》** [arXiv:2607.19727](https://arxiv.org/html/2607.19727v1)；另有原型 [`forgi86/control-theory-in-lean`](https://github.com/forgi86/control-theory-in-lean)、小项目 [`guilhermesilveira/box-lyapunov`](https://github.com/guilhermesilveira/box-lyapunov) | 缺口复用调研记录了该库内容（neighborhood filter 表述的稳定性、一个 Lyapunov 定理同时覆盖点与集合、连续/离散/混合系统、不变集、极限集、LaSalle 不变性原理、小增益定理）。**⚠️ 两处不确定**：(i) 该库的 **GitHub URL 未在 arXiv 正文中直接给出**，文献索引逐字标「具体 URL 未在正文中直接给出，**未确认**」；(ii) `forgi86/control-theory-in-lean` 与该库的关系**未确认**（文献索引第 11 条）。故本项**在取得确切仓库 URL 并完成对抗审查前，按「无可用库」处理** | `[调研代理报告]` **＋** `[需进一步核实]` |
| **离散动力系统（迭代、不动点）** | 是 | **有** | Mathlib 主线 | `Function.iterate` 等为 Mathlib 基础内容；「动力系统」作为成套理论（拓扑共轭、不变集、极限集、分岔）不在 Mathlib——此判断保留 | `[调研代理报告]` |
| **马尔可夫链（定义、转移核）** | 是 | **部分有** | Mathlib 主线 | Mathlib 有 `ProbabilityTheory.Kernel`、`IsMarkovKernel` 等（见 `00-路线图.md` 阶段 1A 输入栏的引用）。本次未逐模块抓取 | `[调研代理报告]` |
| **马尔可夫链遍历性（不可约／非周期／正常返 ⇒ 唯一平稳分布 + $P^n\to\mathbf{1}\pi$）** | 是 | **不确定（须实测）** | **未查到 Lean4 形式化** | 缺口复用调研第五节**未把此项列入「未能确认」清单**，故本项既无正面证据也无反面证据。**保留「不确定」，且为本表最须优先实测的一项**（它是 T5.12 的直接前置） | `[需进一步核实]` |
| **图论基础（无向图）** | 是 | **有** | Mathlib 主线 | `SimpleGraph` 及其配套（连通性、匹配、着色等） | `[调研代理报告]` |
| **DAG / d-分离 / 马尔可夫性** | 是 | **无**（Mathlib） | **Causalean（CausalSmith）**：DAG 为带可判定边关系与存储拓扑序的结构；**d-分离实现为 Bayes-Ball 可达性**；另有 SWIG、c-component 分解。簇规模 465 声明 | 依赖-Causalean 实录：`Causalean.Graph.DAG`（`Graph/DAG.lean:60`）；`DAG.dSep`（`Graph/DSep/Separation.lean:64`）；**`bbReachableVertices_iff_activeWalk`（`DSep/ActivePath.lean:760`）——Bayes-Ball ⟺ 活跃路径，是「证明」不是「假设」**；`globalMarkov`、`full_globalMarkov_with_fixed`、`full_local_markov`；`markovEquiv_iff_sameSkeleton_sameImmoralities`（论文 Table 3 逐个名字**逐字命中**）。该审查方式为 **`git clone` 后 `git ls-tree` / `git show` / 全库 `Select-String` / 解析站点 13.3 MB 机器可读索引** | `[实测仓库文件]` |
| **SCM / 结构方程** | 是 | **无**（Mathlib） | **Causalean** `SCM/` 簇（830 声明） | 依赖-Causalean 实录 `Causalean.SCM` 结构（`SCM/Model/SCM.lean:76`）：随机性**只在潜变量根**，`structFun` 确定性 + 可测；`jointKernel`／`obsKernel`／`obsCondKernel` 全部**派生**而非公设；`evalMap`（沿拓扑序良基递归，`evalMap_measurable`） | `[实测仓库文件]` |
| **do 算子 / 干预** | 是 | **无**（Mathlib） | **Causalean** `fixSet`（定义性别名 `fixMono`，docstring 明写 "Standard (Pearl) multi-target do"） | 依赖-Causalean 实录 `SCM/Model/InterventionSet.lean:57`、`InterventionMono.lean:239`、`swigInterventionSet_insert_equiv` | `[实测仓库文件]` |
| **do-calculus 三条规则** | 是 | **无**（Mathlib） | **Causalean ◐ 部分覆盖** | 依赖-Causalean 实录：`do_rule1`（`SCM/Do/DoCalculus.lean:88`）；`do_rule2_kernel_of_nondescendant_product_ae`（`Do/Rule2AE.lean:164`）；`do_rule3_star`（`DoCalculus.lean:157`）；`do_rule3_star_conditional`（`Rule3Conditional.lean:233`）。**库自己声明**：「They therefore **do not state Pearl's Rules 2 and 3 at their full graphical generality**」（`DoCalculus.lean:13-15`）；Rule 3 的条件「**比 Pearl 完整 Rule 3 更强**」（`Rule3Conditional.lean:20`） | `[实测仓库文件]` |
| **后门准则 / 前门准则** | 是 | **无**（Mathlib） | **Causalean ✅ 完整覆盖** | 依赖-Causalean 实录：后门 `backdoorCriterion`（`SCM/ID/BackdoorCriterion.lean:94`）+ `backdoor_identifiable_ae`（`ID/Backdoor.lean:457`）+ 完备性 `backdoor_completeness_ae`；前门 `frontdoorCriterion`（`ID/Frontdoor/Setup.lean:73`）+ `frontdoor_identifiable_ae`（`Frontdoor/Completeness.lean:133`）。**⚠️ 结论是 `=ᵐ[...]`（a.e. 相等）且带三条绝对连续性前提**；库自承三条前提中「只有中间那条是实质性重叠」 | `[实测仓库文件]` |
| **识别性 / ID 算法** | 是 | **无**（Mathlib） | **Causalean ◐ 部分覆盖（只有可靠性，无完备性，无 hedge 证书）** | 依赖-Causalean 实录：`Identifiable`（`SCM/ID/Identifiable.lean:120`）、`nonIdentifiable_iff`（真正的 hedge 见证形式）、可靠性链 `id_sound`／`id_sound_rec`／`id_sound_discrete`／`idAlgorithm_sound`。**库三次明文声明**：`DoGFormulaRec.lean:16` 「It is used **only in the soundness direction** here; **no converse or formal failure/hedge certificate is claimed**」；`idSucceeds` 自称 "no-additional-fixing **approximation**"。**关键误用后果（M2）**：`idAlgorithm` 返回 `false` 时**不得**声称不可识别 | `[实测仓库文件]` |
| **反事实** | 是 | **无**（Mathlib） | **Causalean ◐ 部分覆盖（无嵌套反事实）** | 依赖-Causalean 实录：`evalMap_fixSet_factual_eq`（`SCM/Model/CounterfactualLemmas.lean:137`）、`evalMap_fixSet_union_eq`、`cutsetLatent`；PO 侧另有 `POSystem.counterfactualDist`。**库自承** `union_eq` 是「带中间值假设的**复合引理**，**不是**次序无关性定理」；`nestedCounterfactual` **0 命中** | `[实测仓库文件]` |
| **条件独立（有限形式）** | 是 | **有部分底层** | **Causalean ✅ 完整覆盖**（99 条声明） | 依赖-Causalean 实录：`FullCondIndep`、`ObsCondIndep`；**半图胚公理逐条证明**（`fullCondIndep_{symm,decomposition,weak_union,contraction,congr_left,congr_right,const_left}`）；底层接 Mathlib 的 `ProbabilityTheory.CondIndepFun` | `[实测仓库文件]` |
| **因果发现的结构学习算法（PC／GES／FCI／CPDAG／Meek）** | 是 | **无**（Mathlib） | **⚠️ 无任何现成实现——真空白** | 独立复核记录（`ref/复核-Causalean核实.md`）以 sparse clone `Causalean/Discovery` 全文检索：`PC\b`=**0**、`FCI`=**0**、`CPDAG`=**0**、`Meek`=**0**、`skeleton`=**0**、`MarkovBlanket`=**0**、`dSep`/`DSep`=**0**。**三个非零命中经逐条核实全部为假阳性**：`GES`(35) 全是英文单词子串（`candidates`／`youngest`／`packages`／`suggests`／`ranges`）；`hedge`(30) 全是 **Lean 变量名**（源自 "hypothesis of **edge**"）；`faithful`(2) 全是 docstring 英文散文。Discovery 簇实为 41 个 `.lean` / 9,300 行，只有 `InvariantPrediction`／`LinearDisentanglement`／`LiNGAM` 三个子目录，即**识别机制理论，不是算法** | `[实测仓库文件]`（**经独立复核**） |
| **泛化界 / Rademacher 复杂度** | 是 | **无**（Mathlib） | **★ 两个成熟库**：① [`auto-res/lean-rademacher`（公开 API 包名 `FoML`）](https://github.com/auto-res/lean-rademacher)，[arXiv:2503.19605](https://arxiv.org/abs/2503.19605)（**已被 ITP 2026 接收**）；② [`YuanheZ/lean-stat-learning-theory`](https://github.com/YuanheZ/lean-stat-learning-theory)，[arXiv:2602.02285](https://arxiv.org/html/2602.02285v1)（**ICML 2026**，约 30,000 行 Lean 4，865 条新定理，470 源文件，自称 **sorry-free**，Lean **v4.32.0** 固定，Apache-2.0） | 缺口复用调研以 `web_fetch` 读一手页面得出。**关键交叉印证**：Causalean 的 `ML/` 簇明确声明 **"uses FoML"**，且 FoML 以 **in-tree vendored**（`third_party/lean-rademacher/`）形式存在并**被 `Stat/Concentration/`、`Estimation/`、`ML/` 消费**——即「Causalean + FoML」已是一个互相衔接的栈。**分工**：FoML 走 Rademacher 复杂度（较松、控制整个函数类）；SLT 走局部化经验过程 + Dudley 熵积分（更紧，且**明确批评前者「rates 松、应用受限」**） | `[调研代理报告]` ＋ `[实测仓库文件]`（FoML 的 vendored 与消费关系） |
| **浮点算术验证** | 是 | **无**（Mathlib） | **FloatLib** [arXiv:2609.19352](https://arxiv.org/html/2609.19352v1) | 缺口复用调研记录其内容：「Lean 4 中**已验证的任意精度浮点算术库**……每个 certified backend 被证明等于完整 encoded specification」。**⚠️ 文献索引与缺口复用调研均未给出其 GitHub 仓库 URL；该库的仓库位置、Lean 版本、许可、sorry 状态均未核实** | `[调研代理报告]` **＋** `[需进一步核实]` |
| **离散化误差界（「连续 → 二值编码」这一步）** | 是 | **无**（Mathlib） | **✖ 无现成项目——真空白** | 缺口复用调研第五节第 8 条逐字：「**适用于「连续→二值编码」的离散化误差界形式化 —— 未查到任何系统中存在**」。**注意区分**：FloatLib 管**算术**误差，`Mathlib.Analysis.ODE.Gronwall` 的 `dist_le_of_approx_trajectories_ODE` 管**ODE 扰动**误差，Coq VeriNum ／Isabelle ITP 2012 提供**方法论范式**（离散化误差与舍入误差分开再合并）——**「把连续对象编码成二值」这一步的误差界，无任何形式化** | `[调研代理报告]` |
| **ILP（归纳逻辑编程）** | 是 | **无**（Mathlib） | **✖ 无现成项目——真空白** | 缺口复用调研第五节第 4、5 条逐字：「**任何 ILP（归纳逻辑编程）形式化项目**（任意证明助手）——未查到」「**「规则空间泛化界」的形式化** —— 未查到」 | `[调研代理报告]` |
| **Datalog / Horn 子句演绎语义** | 是 | **无**（Mathlib） | **◆ 需适配**：[arXiv:2605.02113](https://arxiv.org/abs/2605.02113)（SLE 2026，Datalog 的 Lean 浅嵌入）；[ITP 2025 论文](https://iccl.inf.tu-dresden.de/w/images/d/dc/ITP-2025-Paper-116-Camera-Ready.pdf)（模型论语义与证明论语义的等价，**明确未形式化不动点语义**） | 缺口复用调研记录。**注意边界**：这两项给的是**演绎**语义，**不是归纳**——不能替代 ILP | `[调研代理报告]` |
| **FCA（形式概念分析）** | 是 | **Mathlib 有数学内核，无 FCA 层** | **⏸ 暂缓**（依裁决 H）；公开 Lean4 侧 **无** FCA 形式化 | ① **Mathlib 内核**：`Order.GaloisConnection` 提供 Galois 连接全套理论；FCA 的两个导出算子 $A\mapsto A'$、$B\mapsto B'$ 正是 $\mathcal{P}(G)$ 与 $\mathcal{P}(M)$ 之间的反变 Galois 连接，$X\mapsto X''$ 是闭包算子——**「FCA 的数学内核在 Mathlib 中已具备，缺的只是『形式背景／形式概念／概念格』这一层薄封装」**（缺口复用调研逐字）。② **公开生态**：Lean4 侧**未查到任何** FCA 形式化项目（多轮多关键词检索，含 GitHub／Reservoir／arXiv）。③ Isabelle/HOL 有 Sertkaya & Oğuztüzün 的 Basic Theorem 机器检验证明（ICFCA 2004 / LNCS 3280），**▲ 仅参考**（代码不可移植）；Mizar 有 Schwarzweller 2000（**内容与规模未确认**）。④ **AFP 中是否有 FCA 条目未确认**（fetch 失败） | `[调研代理报告]`（Mathlib 内核判断与「未查到」）＋ `[实测仓库文件]`（裁决 H 对自有库的粗查） |
| **凸优化 / KKT** | 是 | **无**（Mathlib） | **optlib**（[optsuite/optlib](https://github.com/optsuite/optlib)，110★，Apache-2.0）——**但它是 Causalean 的 vendored 依赖** | 依赖-Causalean 实录：`lakefile.toml` 的 require 顺序为 `FoML`（vendored）→ `optlib`（vendored）→ `mathlib`（**必须放最后**）；optlib 在 Causalean 中只携带 KKT 依赖闭包（LICQ／仿射约束资格 + Farkas 引理），**被 `Estimation` 的 minimax 下界消费** | `[实测仓库文件]` |
| **因果推断（Causalean 之外的实现）** | 是 | **无** | **❓ 未查到任何第二实现** | 缺口复用调研第 8 项与文献索引第三批均记为「未查到任何其他的 Lean 4 / Coq / Isabelle 因果推断形式化项目」。**这既是好事（单一权威、无需取舍），也是风险（无第二实现可交叉验证）** | `[需进一步核实]`（未查到 ≠ 不存在） |

### 2.1 表格的读法（五条，第 4、5 条为本次新增）

1. **「部分有」不是「基本可用」。** Mathlib 中存在某方向的若干构件，与「该方向的定理可以拿来做推导」是两件事。凡第二栏填「部分有」者，**一律按「核心需补」处理**。
2. **第二栏的时效性。** Mathlib 内容随时间增长，上表的「无／部分有」可能变化。**但这一变化不影响本路线在因果层的决策**：因果推断不在 Mathlib 的选题范围内，其增长瓶颈是范围而非时间。**唯一存在的「上游会补上」的情形是随机分析一侧**——而这已被实测证实：布朗运动与鞅收敛**已经补上了**。
3. **「不确定」项的处理。** 本表标 `[需进一步核实]` 者共四处：**SDE 强解存在唯一性、马尔可夫链遍历性、Lyapunov 库的确切仓库与可用性、FloatLib 的仓库位置**。**这四项不构成阻塞，但构成本文件的使用限制**：把其中任何一项作为「已有、可直接依赖」来安排工作量，都是**未经核实的假设**。正确的做法是：开工前先做一次针对性实测。**本机已具备该实测条件（见第五节）。**
4. **（新增）第三栏为空不等于第二栏为空。** 一个对象可以「Mathlib 无、生态无」，此时才须自建；也可以「Mathlib 无、生态有」，此时**复用的优先性高于自建**（依裁决 G 第 4 条：「缺口部分也要看有没有现成项目，一切能复用就复用」）。**本表中属于后者的有八项**：DAG/d-分离、SCM、do 算子、后门/前门、识别性、反事实、条件独立、泛化界。
5. **（新增）第三栏非空不等于可依赖。** 依裁决 G 第 2、3 条，**任何外部依赖须先过对抗性审查与准入门槛（第六节）**。本表中 `▲ 仅参考` 者（Isabelle/Mizar 的 FCA、Coq VeriNum、Isabelle ODE）**代码不可移植，只能参考定理陈述与证明策略**；`[需进一步核实]` 者**在核实前视同无现成库**。

---

## 三、依赖分层（新章节，核心）

依**作者裁决 G**（「所有外部依赖单独写一个文档，标明用了什么、用来干什么」「所有外部依赖库需要进行对抗性审查」「一切能复用就复用」），本节把本路线的**全部**外部依赖分层登记。

### 3.1 依赖分层表

| 层 | 依赖 | 用途 | 被谁用 | 状态 |
|---|---|---|---|---|
| **L1 基础** | **Mathlib** | 基础数学：测度论、概率论、序论（Galois 连接/闭包算子/完备格）、ODE（Picard–Lindelöf、Grönwall）、鞅与鞅收敛、**布朗运动**、`Quotient`/`Setoid`、`Computability` | 全部层、全部章节 | **已核实（部分）**：抓取 `Probability.BrownianMotion.Basic`、`Probability.Martingale.Convergence`、`Analysis.ODE.Gronwall` 三页均 HTTP 200 并读到签名；**其余模块仍为报告级**。**版本：master `v4.35.0-rc4`** |
| **L1 基础** | **Causalean（CausalSmith）** | 因果推断形式化：DAG／d-分离／Bayes-Ball／SWIG／c-components、SCM、do 算子、do-calculus（R1 完整、R2/R3 受限）、后门／前门、ID（仅可靠性）、部分识别、潜在结果、反事实（无嵌套） | **第 3 章、第 6 章**（及第 7 章的反事实边界） | **已对抗审查**（两轮：审查 + 独立复核）。**版本：Lean `v4.33.0`，Mathlib pin `db584cd6…`**；HEAD `47acf195…`（2026-10-07）；站点索引 commit `2adec37…` |
| **L2 次级** | **FoML / `lean-rademacher`** | Rademacher 复杂度泛化界、对称化、McDiarmid、Dudley 熵积分、VC | **误差界（第 7 章 L7）**；**且已被 Causalean 的 `Stat/Concentration/`、`Estimation/`、`ML/` 消费** | **需单独建档**（依裁决 G 第 2 条）。**同时是「vendored 依赖」，见 3.2**。版本：Lean `v4.32.0`；MIT（adapted）；23★ |
| **L2 次级** | **`lean-stat-learning-theory`** | 统计学习理论：高维 Gauss Lipschitz 集中、**Dudley 熵积分定理**、局部化经验过程、最小二乘（稀疏）回归的尖锐速率 | **误差界（第 7 章 L7）**——若需更紧的速率则优先用它，FoML 作为接口更简单时的备选 | **需单独建档**。版本：Lean `v4.32.0`；Apache-2.0；据报告 ~30,000 行 / 865 定理 / **自称 sorry-free** |
| **L2 次级** | **FloatLib** | 已验证的任意精度浮点算术、真实舍入与误差界 | **数值误差（第 7 章 E2 类）**；对应 `Equivalence`（序 13）的浮点偏差条款 | **待审**（依裁决 G 第 3 条）。**⚠️ 仓库位置未定位**；Lean 版本、许可、sorry 状态**均未核实** |
| **L2 次级** | **`RemyDegenne/brownian-motion`** | 随机分析：布朗运动完整构造（Kolmogorov 扩张 + Gaussian Banach 空间测度 + Kolmogorov–Chentsov）；**随机积分与 Itô 引理进行中** | **连续情形**：`Stochastic`（序 12）、`Fate` 的路径测度、T0.2、T5.2、T5.16 | **待审**。布朗运动部分**已迁入 Mathlib**（见第二节实测）；Itô 部分**未完成、未进 Mathlib**。Apache-2.0；62★ |
| **L2 次级** | **optlib（OptSuite）** | KKT 一阶必要条件（LICQ／仿射约束资格）+ Farkas 引理 | **仅被 Causalean 的 `Estimation` minimax 下界消费** | **待审**（依裁决 G 第 3 条）。**同时是「vendored 依赖」，见 3.2**。Apache-2.0；110★ |
| **vendored** | **FoML（in-tree 副本）、optlib（in-tree 副本）** | 见上两行 | **被 Causalean 内部消费** | **「依赖的依赖」——见 3.2，须各自单独建档** |
| **▲ 仅参考** | Isabelle Sertkaya (ICFCA 2004)、Mizar Schwarzweller 2000 | FCA 基本定理的定理陈述与证明策略 | `FCA`（序 9，暂缓中） | **代码不可移植** |
| **▲ 仅参考** | Coq VeriNum、Isabelle ITP 2012（Immler–Hölzl） | 分层误差分解范式（离散化误差与舍入误差分开再合并） | **离散化误差界（T5.4／T5.5／T7.10）** | **代码不可移植** |
| **▲ 仅参考** | CausalSmith 流水线的方法论 | 四类失败模式、逻辑图、库反馈、`gated`/`cited` 标记、机械禁用记号扫描 | **全部自建库的验收流水线** | **机制可移植，代码不适用** |
| **▲ 仅参考** | Lean Machine Learning (LML) | 随机序贯算法框架、bandit 遗憾界 | 如本理论涉及序贯决策／在线学习 | **仓库 URL 与规模未能确认** |

### 3.2 vendored 依赖的处置（必须写明的规则）

**Causalean 携带两个 in-tree vendored 外部依赖**（证据：依赖-Causalean §1.5，从仓库 `lakefile.toml` 与 `lake-manifest.json` 直接读出）：

| 依赖 | 来源 | 许可证 | 在 Causalean 中的用途 | 上游状态 |
|---|---|---|---|---|
| **FoML** = `lean-rademacher` | [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher)（23★，MIT，2026-09 更新） | MIT（adapted） | Rademacher 复杂度、McDiarmid、对称化、Dudley 熵积分；被 `Stat/Concentration/`、`Estimation/`、`ML/` 消费 | 以 in-tree 副本携带（`third_party/lean-rademacher/`），有 `UPSTREAM.md` |
| **optlib** | [optsuite/optlib](https://github.com/optsuite/optlib)（110★，Apache-2.0） | Apache-2.0（adapted） | KKT 一阶必要条件（LICQ／仿射约束资格）+ Farkas 引理；被 `Estimation` 的 minimax 下界消费 | 只携带 KKT 依赖闭包，bumped 到 Mathlib pin |

> **规则（依裁决 G 第 2、3 条）**：**vendored 依赖是「外部依赖的依赖」，它不因被裹进上游仓库而免于审查。** 具体地：
>
> 1. **FoML、optlib（在 Causalean 的 in-tree 副本）须各自单独建档**——记入 `ref/依赖登记.md`，并各自做八问对抗性审查（依裁决 G 第二节）。
> 2. **须核对 in-tree 副本与上游的差异**：Causalean 的副本是否被修改过？是否跟随上游？`UPSTREAM.md` 记录了什么？**in-tree 副本的「认证等级」不能高于上游本身。**
> 3. **若本路线直接依赖上游 FoML**（而非透过 Causalean），则**直接依赖与 vendored 副本是两份不同的代码**，二者的版本可能不同——**这本身是一条版本风险**（见第五节）。
> 4. **凡未登记的依赖不得出现在证明中**（依裁决 G 第五节执行纪律）。

### 3.3 一条架构级风险（承自对抗审查，须在本文件登记）

> **Causalean 内并存两套不等价的框架**：`SCM` 簇（830 声明）与 `PO` 簇（1,847 声明）。**二者不是自动等价的**（依赖-Causalean 问 3、误用风险 M7）。

**本路线的处置**：**必须先在本路线内选定一个权威记号**（候选：对第 3 章取 `SCM` 簇，对第 7 章的反事实边界取 `PO` 簇），**并在 `01-定理清单.md` 的对应条目上标注所用框架**。若不先固定，将积累**未被证明的隐含假设**——这属于内核查不出的那类错误。

### 3.4 三个同名不同义的陷阱（高危，直接导致误用）

承自对抗审查并经独立复核确认，**在检索与引用 Causalean 时必须逐条规避**：

| 记号 | 陷阱 | 复核结果 |
|---|---|---|
| **`hedge`** | SCM／Graph 中 **315 处**命中**全部是 tactic 局部变量名**，意为 "hypothesis of **edge**"（`have hedge_j : ...`）。**因果推断意义上的 hedge（不可识别的见证结构）在库中不存在** | ✅ 独立复核确认（`Causalean/Discovery` 内 30 处全为 Lean 变量名） |
| **`Lyapunov`** | **3 处命中全是 Lyapunov CLT 的矩条件**（`Stat/IndependentTriangularArray.lyapunov_clt`、`lyapunovSum` 等），**与 Lyapunov 稳定性／Lyapunov 函数毫无关系** | 审查记录 |
| **`stochasticIntegral`** | **5 处命中不是 Itô 积分**，是 `Stat/RecurrentEvent/CountingProcess/FiniteJump/` 里**有限跳计数过程的补偿子积分**（Nelson–Aalen） | 审查记录 |
| **`GES`** | 在 `Discovery` 簇内 **35 处命中全是英文单词子串**（`candidates`／`youngest`／`packages`／`suggests`／`ranges`）；文献索引另记 12 处为 `weaklyConverges`/`largeSample` 子串 | ✅ 独立复核确认 |
| **`dSep`** | 其定义**内建 pairwise disjointness**（`Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ …`），**只能对互不相交的查询集陈述**。若本框架需要对相交集合说 d-分离，**用不了它**；改写后不再是库里的 `dSep`，之前的定理全部失效 | 审查记录 |
| **`MarkovEquiv`** | 是**语义定义**（d-分离相等），「同骨架同 immoralities」是**定理**而非定义 | 审查记录 |

---

## 四、自建范围（大幅缩减并重估）

### 4.1 排列原则与量级定义

本节按**依赖顺序**排列，规则三条：**被依赖者在前；定义先于定理；本理论特有对象最后**。

| 量级 | 含义 |
|---|---|
| **胶水代码** | 主要是把已有对象按新名字重新组织，或填少量结构字段；证明多为 `rfl`、`exact`、字段展开与少量引理组合；不做新的数学论证。 |
| **小项目** | 需自行设计若干定义并证明一批基本引理（约数十条），但每条的证明都不超出标准教科书习题的难度；无新的数学洞察。 |
| **中等项目** | 定义层有实质的设计选择（如「干预」的表示形式会影响后续全部定理的陈述），定理层有若干需要真正论证的引理；存在局部可能卡住的地方。 |
| **大项目** | 涉及成套理论的形式化，其中若干步骤可能需要新的技术手段或依赖尚不具备的底层设施；存在「无法在合理范围内完成」的风险。 |
| **研究级** | 该理论在**数学文献中亦无现成的、可直接转写的成形体系**，或需在离散结构空间等非标准载体上重建整套理论；**其完成不取决于工作量投入，而取决于是否出现关键的新技术手段**。**这一档的判定必须逐项标注依据**（依裁决 C 第四节第 4 条）。 |

### 4.2 原 11 个规划库的逐项处置（依实测结果）

| 原规划库 | 实测处置 | 依据 |
|---|---|---|
| **`Causality.Graph`** | ✅ **复用 Causalean**（不再自建） | Graph 簇 465 声明；`DAG` 带可判定边关系与存储拓扑序；`dSep` 定义为 Bayes-Ball 可达；**`bbReachableVertices_iff_activeWalk` 证明 Bayes-Ball ⟺ 活跃路径**；`markovEquiv_iff_sameSkeleton_sameImmoralities` 逐字命中论文 Table 3。`[实测仓库文件]` |
| **`Causality.SCM`** | ✅ **复用 Causalean**（不再自建） | `SCM` 结构（`Model/SCM.lean:76`）：随机性只在潜变量根，`structFun` 确定性+可测；`jointKernel`/`obsKernel`/`obsCondKernel` 全部**派生**而非公设；`evalMap` 沿拓扑序良基递归且可测。`[实测仓库文件]` |
| **`Causality.Do`** | ◐ **复用 + 适配**（R2/R3 非 Pearl 完整图形一般性） | `fixSet`（= SWIG 节点分裂）与 `fixMono` 可用，docstring 明写 "Standard (Pearl) multi-target do"；**但** do-calculus 侧 R2/R3 受限（库自承）。`[实测仓库文件]` |
| **`Causality.CondIndep`** | ✅ **复用 Causalean**（不再自建） | `FullCondIndep`／`ObsCondIndep`；**半图胚公理七条逐条证明**；CondIndep 家族 99 条；底层接 Mathlib `CondIndepFun`。`[实测仓库文件]` |
| **`Causality.Identification`** | ◐ **复用 + 补**（**只有可靠性，无完备性，无 hedge**） | `Identifiable` + 可靠性链齐备；**无完备性**、失败时不产出 hedge 证书（库三次明文声明）；`idSucceeds` 自称 "no-additional-fixing approximation"。**这是本路线在因果层唯一必须自补的实质缺口**。`[实测仓库文件]` |
| **`Causality.DoCalculus`** | ◐ **复用 + 补**（同上；R1 完整，R2/R3 需推广到 Pearl 完整图形一般性） | `do_rule1` 完整；`do_rule2_kernel_of_nondescendant_product_ae`／`do_rule3_star_conditional` 的前提**比 Pearl 原版更强**。`[实测仓库文件]` |
| **`Causality.Counterfactual`** | ◐ **复用 + 适配**（无嵌套反事实） | `evalMap_fixSet_factual_eq` 等可用；`nestedCounterfactual` **0 命中**；`union_eq` 库自承「不是次序无关性定理」。`[实测仓库文件]` |
| **`Causality.Discovery`** | ⚠️ **降级为参考**（不作复用对象） | **实测零结构学习算法**：`PC\b`／`FCI`／`CPDAG`／`Meek`／`skeleton`／`MarkovBlanket` **全 0 命中**；三个非零命中（`GES`=35、`hedge`=30、`faithful`=2）**经独立复核全部判定为假阳性**（`GES`→`candidates`/`youngest`/`packages`/`suggests`/`ranges`；`hedge`→Lean 变量名；`faithful`→docstring 英文散文）。实为 ICP + LiNGAM + 线性解缠的**识别理论**。**⚠️ 最高风险项（R-Discovery）**。`[实测仓库文件]`（经独立复核） |
| **`FCA`** | ⏸ **暂缓**（依裁决 H） | 裁决 H：`level0000x/lattice` **暂时先当没有**，待作者整理后再判定「自有库可复用多少、还缺什么」。**但须标注：Mathlib 已有数学内核**（`Order.GaloisConnection` + 闭包算子 + 完备格），故**自建成本低于原估**——这一判断独立于自有库是否可用。`[调研代理报告]` |
| **`Rules`** | ❌ **仍需自建**（ILP 归纳是真空白） | 缺口复用调研第五节第 4、5 条：**任意证明助手中均未查到 ILP 形式化，亦未查到「规则空间泛化界」的形式化**。演绎侧有 Datalog 浅嵌入（`◆ 需适配`），但**不构成归纳**。`[调研代理报告]` |
| **`Fate`** | ❌ **仍需自建**（本理论特有） | 无先例。`[调研代理报告]` |
| **随机分析（拟新增）** | ⚠️ **改为复用 + 补缺口**（**与裁决 C 冲突，标为待裁决**） | **布朗运动已在 Mathlib 主线**（`IsBrownianReal`／`IsPreBrownianReal`，实测文档页）；**鞅收敛（Doob）已在 Mathlib**（`Submartingale.ae_tendsto_limitProcess` 等，实测文档页）；**ODE/Grönwall 已在 Mathlib**（实测文档页）。**Itô 积分 Mathlib 无（实测 404）**，但上游 `RemyDegenne/brownian-motion` 项目**进行中**。**详见 4.4 的冲突声明。** `[实测文档页]` |
| **离散化误差界** | ❌ **仍需自建**（真空白） | 缺口复用调研第五节第 8 条：「**适用于「连续→二值编码」的离散化误差界形式化 —— 未查到任何系统中存在**」。`[调研代理报告]` |

**净结论：原 11 个规划库中，3 个可原样复用（Graph／SCM／CondIndep），4 个需适配后复用（Do／Identification／DoCalculus／Counterfactual），1 个降级为参考（Discovery），1 个暂缓（FCA），2 个仍需自建（Rules／Fate）；另加随机分析由「自建」改为「复用 + 补缺口」、离散化误差界仍须自建。**

### 4.3 重估后的自建清单与规模分布

**重估后的自建库从 13 个减至 6 个**（旧版 13 个为：`Causality.Graph`、`Causality.SCM`、`Causality.Do`、`Causality.CondIndep`、`Causality.Identification`、`Causality.DoCalculus`、`Causality.Counterfactual`、`Causality.Discovery`、`FCA`、`Rules`、`Fate`、`Stochastic`、`Equivalence`）：

| 序 | 库名 | 内容 | 规模估计 | 规模依据 | 优先级 |
|---|---|---|---|---|---|
| **1** | **`Rules`** | 规则作为实例的商；$\alpha$（**FCA 取概念过程**，存在性由 FCA 基本定理保证）；$\gamma$ 的三条判据；$\circ$ 的语义与封闭性；泛化复杂度量 $\mathfrak{C}$。**含 ILP 归纳层** | **中等项目（定义层）＋大项目（语义层）＋研究级（泛化层）** | **定义层**：类型声明、商集、评价量可写出（依据：主文档第 5 章的形状）。**语义层**：$\gamma$ 三判据与 $\circ$ 语义**须从零设计**，原文一个性质也没有（依据：主文档开放问题 5.1、约定 5.2）。**泛化层**：$\mathcal{R}$ 是**离散结构空间**而非函数空间，标准 VC/Rademacher 理论不直接适用；**ILP 归纳的「搜索／覆盖／泛化」在任意证明助手中零形式化**（依据：缺口复用调研第五节的「未查到」）——**改判为研究级** | 高（规则层是主链起点） |
| **2** | **`Fate`** | 状态空间、时间索引集、轨迹、轨迹生成器 $F_{\text{traj}}$、核心方程 (1.1)/(1.2)、观测层 | **小项目（定义层）／中等项目（存在性层）** | **定义层**：轨迹即函数，$F_{\text{traj}}$ 即序列空间→轨迹空间的算子（依据：T0.1、T0.3 的形态）。**存在性层**：**路径测度不必自建**——实测确认 Mathlib 已有布朗运动与鞅收敛，`MeasureTheory` 已有乘积测度／Kolmogorov 相关设施（依据：第二节实测；**该处依据强度为 `[调研代理报告]`，须实测**）。故由旧版的「大项目」**下调为中等项目** | 高 |
| **3** | **`Discretization`**（**新立**，旧版散落在 `Rules` 的编码算子层与 `Stochastic` 的离散化组） | **「连续 → 二值编码」的误差理论**：编码算子 $\mathrm{enc}$／解码 $\mathrm{dec}$ 的显式构造、阈值非退化条件、误差界 $\sup_x \mathrm{diam}\,\mathrm{enc}^{-1}(\mathrm{enc}(x))\le g(\gamma,\ \text{属性个数})$；**以及 Euler–Maruyama 型离散化误差界** | **大项目** | **实测确认为真空白**：缺口复用调研第五节第 8 条「适用于『连续→二值编码』的离散化误差界形式化 —— 未查到任何系统中存在」。**可借的只有两个局部工具**：Mathlib 的 `dist_le_of_approx_trajectories_ODE`（近似解与真解距离的显式 Grönwall 界，**实测文档页确认存在**）与 Coq VeriNum 的**分层误差分解范式**（▲ 仅参考）。**判为大项目而非研究级**：其数学内容为阈值化算子的胞腔直径估计，属初等分析（依据：`04-误差界路线.md` $\textsf{E}_8$） | **高**（它是 A32 的落点，且是 `Rules` 编码算子层的唯一硬前置） |
| **4** | **`Causality.IDCompletion`**（**新立**，旧版无此项） | **补 Causalean 在识别层的四处缺口**：(i) ID 算法的**完备性**；(ii) 失败时的 **hedge 证书**；(iii) do-calculus **R2/R3 推广到 Pearl 完整图形一般性**；(iv) **嵌套反事实** | **大项目** | **依据**：库自承的三处声明（`DoGFormulaRec.lean:16`、`IDAlgorithmRec/Soundness.lean:19-21`、`DoCalculus.lean:13-15`）构成**明确的、有位置的缺口**。**判为大项目而非研究级**：Pearl 的 ID 完备性（Shpitser–Pearl）与 hedge 判据在**文献中已有成形证明**可转写（依据：`01-定理清单.md` T3.11 把该证明的路线记为「hedge／嵌套 do 表达式正规形」）——**困难在转写而非在数学** | **中**（因果走旁路，依 `00-总纲.md` 第二节；但依裁决 C「不降级」，本项仍为必做） |
| **5** | **`FCA`** | 形式背景、导出算子对、形式概念、概念格、属性蕴含、DG 基；$\alpha$ 取概念过程接口 | **⏸ 暂缓**（规模待自有库整理后重估） | 依**裁决 H**：`level0000x/lattice` 暂不引入，FCA 部分按「无现成库、需自建」处理；**但 Mathlib 已有数学内核**（Galois 连接 + 闭包算子 + 完备格），故**自建成本低于原估**——「FCA 的数学内核在 Mathlib 中已具备，缺的只是形式背景／形式概念／概念格这一层薄封装」（缺口复用调研逐字）。**⚠️ 该「薄封装」判断源于推理而非 Lean FCA 论文**（缺口复用调研自己声明「此判断是基于 Mathlib 已有 Galois 连接与完备格理论的**推理**」） | **暂缓** |
| **6** | **`Equivalence`** | 目标语言语义片段 + refinement 论证 + 「手写实现 ≡ 提取实现」的等价性定理 | **大项目** | **依据**：Mathlib 生态内**不存在** Python／C++ 等形式化目标语言语义层（依据：Mathlib 选题范围为经典数学分支这一长期事实）。**本项规模未因本次调研而下调**——第二、三节列出的全部现成库中**没有一个**提供目标语言语义层 | 高（依裁决 C，阶段 4 必做） |

**规模分布（6 个库）**：

| 规模档 | 库 | 数量 |
|---|---|---|
| **胶水代码** | — | 0 |
| **小项目** | `Fate`（定义层） | 1 |
| **中等项目** | `Rules`（定义层）、`Fate`（存在性层） | 2 |
| **大项目** | `Rules`（语义层）、`Discretization`、`Causality.IDCompletion`、`Equivalence` | 4 |
| **研究级** | `Rules`（泛化层） | 1 |
| **暂缓** | `FCA` | 1 |

**两条读数**：

1. **旧版 13 个库中，7 个整体消失**（`Causality.Graph`／`SCM`／`Do`／`CondIndep`／`Identification`／`DoCalculus`／`Counterfactual` —— 前四个整体复用、后三个由新立的 `Causality.IDCompletion` 承接适应性补缺）。**这不是「工作量消失了」，而是「工作量转移到了复用与适配」**：从「从零写一个库」变为「读懂一个 15,821 条声明的库、过准入门槛、补四处缺口」。
2. **旧版的 `Stochastic`（大项目到研究级）整体消失**，其内容被三处吸收：**复用 Mathlib**（布朗运动、鞅、鞅收敛、ODE/Grönwall）、**跟进上游**（Itô 积分 → `RemyDegenne/brownian-motion`）、**自建**（离散化误差界 → 新立的 `Discretization`）。**这是本次重估中幅度最大的一处。**

### 4.4 ⚠️ 与作者裁决 C 的冲突（如实报告，标为待作者裁决）

> **本节是本文件与最高优先级裁决之间的唯一实质冲突。本文件不擅自推翻裁决 C，只如实报告冲突并给出建议。**

**裁决 C 的原文要求**（[`../03-规范与裁决/01-作者裁决C-最彻底.md`](../03-规范与裁决/01-作者裁决C-最彻底.md) §一第 3 行、§三）：

> | 「连续情形（SDE）降级为登记」 | **撤销**。**自建随机分析库**，连续情形全量形式化 |
> | `proof/02-Mathlib缺口.md` | 自建随机分析库正式纳入；`Rules`/`Fate` 不再标「空壳」，改为「待理论补完后建」 |

**裁决 C 作出时的事实基础**：当时本文件对 Mathlib 随机分析一侧的判断为「**部分有（随机分析雏形）**……成熟度不足以支撑常规使用……**明确标注：不确定。使用前必须实测**」（旧版 §二 SDE 行）。

**后续实测推翻的事实基础**：

| 旧的判断（裁决 C 所依据） | 实测结果 | 证据强度 |
|---|---|---|
| 布朗运动「部分有（构造存在）；成套性质**不确定**」 | **`IsBrownianReal` 与 `IsPreBrownianReal` 均为 Mathlib 主定义**；独立增量、弱 Markov 性、协方差 `min s t`、尺度不变、反演不变、a.s. 连续路径**均有定理** | `[实测文档页]` |
| 鞅收敛「**不确定**」；「Doob 分解与收敛定理不确定」 | **`Submartingale.ae_tendsto_limitProcess`（a.e. 鞅收敛）、`tendsto_eLpNorm_one_limitProcess`（L¹ 鞅收敛 a）／`ae_eq_condExp_limitProcess`（b）／`tendsto_ae_condExp`＋`tendsto_eLpNorm_condExp`（c）全部存在** | `[实测文档页]` |
| SDE 侧「LipschitzWith、Gronwall 部分齐备」 | **`Mathlib.Analysis.ODE.Gronwall` 完整**：`gronwallBound`、`norm_le_gronwallBound_of_norm_deriv_right_le`、**`dist_le_of_approx_trajectories_ODE`**、`dist_le_of_trajectories_ODE` 及其 `_of_mem` 变体；**另有 `Mathlib.Analysis.ODE.PicardLindelof`**（报告级） | `[实测文档页]`（Gronwall）／`[调研代理报告]`（Picard–Lindelöf） |
| Itô 积分「远未齐备」 | **Mathlib 确认无**（抓取 `.../ItoIntegral.html` 返回 **404**）；但 **`RemyDegenne/brownian-motion` 项目正在建**（README 逐字：building the necessary theory to define the integral against a semi-martingale） | `[实测文档页]`（404）＋`[调研代理报告]`（上游状态） |

**冲突的实质**：裁决 C 命令「**自建**随机分析库，连续情形全量形式化」。但实测显示，该库**八成以上的内容已经存在于 Mathlib 主线或已有的公开项目线中**。若照裁决 C 原文执行「自建」，其实际工程含义将不是「从零建造」，而是**「重写 Mathlib 已有的布朗运动与鞅论」**——这在工程上是负收益的，且与同日期的**裁决 G 第 4 条「一切能复用就复用」直接冲突**。

**本文件的建议（标为待作者裁决，本文件不自行采纳）**：

> **建议将连续情形的处置由「自建随机分析库」改为「复用 + 补缺口」**，具体为四步：
>
> | 原裁决 C 的「自建 `Stochastic`」八组内容 | 建议处置 | 依据 |
> |---|---|---|
> | 布朗运动（构造、独立增量、高斯性、马尔可夫性、自相似、反射原理、**无处可微**） | **复用 Mathlib**（`IsBrownianReal` 全套）；「**无处可微**」一项**未在实测文档页中出现，须单独实测** | `[实测文档页]` ＋ `[需进一步核实]`（无处可微） |
> | 鞅收敛（a.s. 与 $L^p$） | **复用 Mathlib**（`Submartingale.*` 全套） | `[实测文档页]` |
> | **Doob 分解** | **Mathlib 未在实测文档页中出现**，但 `RemyDegenne/brownian-motion` 的 blueprint **第 2 部分含 Doob–Meyer 定理（离散 Doob 分解、Komlòs 引理、局部版本）**——**须实测或跟进上游** | `[调研代理报告]` |
> | SDE 强解存在唯一性 | **复用 Mathlib 的 `Gronwall` + `PicardLindelof` 作为证明工具**；SDE 本身的存在唯一性**未查到任何 Lean4 形式化**——**这是真正的缺口，须自建**（但规模因工具齐备而显著小于旧估） | `[实测文档页]`（工具）＋`[需进一步核实]`（SDE 本身） |
> | Itô 积分、Itô 引理 | **跟进 `RemyDegenne/brownian-motion`**（进行中，未进 Mathlib）——**不平行自建**。若须独立可用，则须以协作者身份复用其未发布代码 | `[调研代理报告]` |
> | Fokker–Planck（含 A34 转移密度存在且光滑） | **仍须自建**（Mathlib 无）；但 A34 的证明路线可由 Mathlib 的椭圆正则性相关设施支撑——**须实测** | `[需进一步核实]` |
> | 马尔可夫链遍历性 | **仍须自建或找到现成库**——**未查到任何 Lean4 形式化**；这是本项中第二大的真缺口 | `[需进一步核实]` |
> | Euler–Maruyama 离散化 | **仍须自建**，归入新立的 `Discretization` 库 | `[调研代理报告]` |

**同时须写明三条，以免本建议被误读**：

1. **本建议不构成「降级」。** 裁决 C 撤销的是「**降级为登记**」（即不形式化）；本建议仍要求**连续情形全量形式化**——只是形式化的**方式**由「自建」改为「复用 + 补缺口」。**「不降级、不移出」的精神完全保留。**
2. **本建议不减少必做条的清单。** `01-定理清单.md` 中 T5.2（SDE 强解存在唯一性）、T5.10（Hartman–Grobman）、T5.11（Lyapunov 指数与混沌）、T5.16（Itô 引理）**仍全部为必做**。本建议只改变它们的**起点**：T5.2 从「先建 Itô 积分理论」变为「以 Mathlib 的 Gronwall／Picard–Lindelöf 为工具、并跟进上游的 Itô 线」。
3. **本建议的生效前提是完成第六节的准入门槛。** 在 `lake build` 与 `#print axioms` 通过之前，**上述「可复用」的判断本身仍是假设**。

**待作者裁决项（登记）**：

| 编号 | 待裁决事项 | 本文件的建议 | 冲突对象 |
|---|---|---|---|
| **Q-C1** | 连续情形是「自建随机分析库」还是「复用 Mathlib + 跟进上游 + 补缺口」 | **建议后者**（理由见上表） | 裁决 C 表第 3 行 |
| **Q-C2** | 若采纳 Q-C1，`Stochastic` 是否仍作为独立库立项 | **建议拆为两支**：复用部分不立项；**须自建部分（SDE 存在唯一性、Fokker–Planck、马尔可夫链遍历性、离散化）并入 `Discretization` 与新立的 `Stochastic.Gap`** | 裁决 C 表第 3 行、`00-路线图.md` P5 行 |
| **Q-C3** | `Fate` 的存在性层规模是否由「大项目」下调 | **建议下调**（路径测度可复用 Mathlib）——**但须先实测** | 裁决 C 表第 3、4 行 |

---

## 五、跨库版本冲突（新章节，阻塞项）

### 5.1 实测数据

数据来源：[`../04-文献与依赖/04-跨库版本对齐风险.md`](../04-文献与依赖/04-跨库版本对齐风险.md)（自述核实方式为**直接 `Invoke-WebRequest` 拉取各仓库的 `lean-toolchain` 文件**，非推测、非二手转述）。

| 库 | 固定 Lean 版本 | 来源 | 证据强度 |
|---|---|---|---|
| **Mathlib master** | `leanprover/lean4:v4.35.0-rc4` | 官方仓库 `lean-toolchain` | `[实测仓库文件]`（经代理） |
| **Causalean** | `leanprover/lean4:v4.33.0` | CausalSmith 仓库 `lean-toolchain`（依赖-Causalean 另有 `Mathlib rev = db584cd6d46c92f209a44c0f1c829460d327499d`） | `[实测仓库文件]` |
| **lean-stat-learning-theory** | `leanprover/lean4:v4.32.0` | 仓库 `lean-toolchain` | `[实测仓库文件]` |
| **lean-rademacher**（FoML） | `leanprover/lean4:v4.32.0` | 仓库 `lean-toolchain` | `[实测仓库文件]` |

### 5.2 问题的性质

Lean4 生态中，**每个库固定一个 Lean 版本**（`lean-toolchain`），且其 Mathlib 依赖也固定在该版本对应的 commit 上。**一个下游项目只能选一个 Lean 版本**，所有依赖必须与之兼容。

```
v4.32.0  ← lean-stat-learning-theory, lean-rademacher (FoML)
   ↓ (差 1 个 minor)
v4.33.0  ← Causalean
   ↓ (差 2 个 minor)
v4.35.0-rc4  ← Mathlib master（最新）
```

**落差最大 3 个 minor 版本。**

**为什么这是阻塞性的**：

- Mathlib 的 API 在 minor 版本间**会变**（改名、改签名、废弃）。实测已提供一处直接证据：抓取到的 `Mathlib.Probability.Martingale.Convergence` 文档页中，`MeasureTheory.tendsto_of_uncrossing_lt_top` 被标为 `@[deprecated ... (since := "2026-09-17")]`，其现行名为 `MeasureTheory.tendsto_of_upcrossings_lt_top`——**一次改名，发生在 2026-09-17**。这正是「版本漂移会静默打断证明」的实例。
- 若下游固定 `v4.32.0`，则只能用 `v4.32.0` 时代的 Mathlib——**拿不到布朗运动之后的更新**（而布朗运动恰恰是本路线最需要的）。
- 若下游升到 `v4.35.0-rc4`（跟进 Mathlib master），则 **Causalean（v4.33.0）与两个 SLT 库（v4.32.0）无法直接作 lake 依赖**。
- **这三块不能同时作为 lake 依赖共存于一个项目**，除非：（1）上游库各自升级并重新对齐，或（2）下游自行 fork 并移植。

### 5.3 与本路线的关联

| 用途 | 拟用库 | 锚定版本 | 受阻情况 |
|---|---|---|---|
| 因果推断（SCM/do/识别/部分识别） | Causalean | `v4.33.0` | 与 Mathlib master 差 2 个 minor |
| 误差界／泛化界／Rademacher | lean-stat-learning-theory 或 lean-rademacher | `v4.32.0` | 与 Mathlib master 差 3 个 minor；与 Causalean 差 1 个 |
| **布朗运动、鞅、鞅收敛、ODE/Grönwall** | **Mathlib 主线** | `v4.35.0-rc4` | 与 Causalean 差 2 个、与 SLT 差 3 个 |
| 基础数学 | Mathlib | `v4.35.0-rc4` | 同上 |

> **即：本路线最想复用的三块（因果、SLT、随机分析）各自锚在不同版本上，且落差最大达 3 个 minor。**

### 5.4 可选方案（待裁决）

**方案 1：跟随 Causalean 的版本（`v4.33.0`）**
- 优点：因果部分直接可用；SLT 落差 1 个 minor，移植成本较低。
- 缺点：放弃 Mathlib master 的新内容；**须把 SLT 库移植到 `v4.33.0`**。
- 适用：若因果部分是主线承重。**注意**：依 `00-总纲.md` 第二节裁决 A，因果已走**旁路**，故此项权重下降。

**方案 2：跟随最新 Mathlib（`v4.35.0-rc4`）**
- 优点：基础库最新；**布朗运动／鞅／鞅收敛直接可用**（这三项恰是本路线的硬需求）。
- 缺点：Causalean 与两个 SLT 库**均需移植**（落差 2–3 个 minor）。
- 适用：若基础与随机分析是主线承重。**本文件倾向此方案**（理由：布朗运动与鞅已在主线，而因果走旁路；但这是路线决策，须由作者裁决）。

**方案 3：等待上游对齐**
- 观察上游是否跟进；**不可作为计划的前提**（无时间保证）。**且 Causalean 的规模在半年内由 7,035 → 8,179 → 15,821，其自身的快速迭代使其对齐 Mathlib master 的动机不明。**

**方案 4：分层——不自建单一项目，而是做「移植层」**
- 各库分别在**自己的版本**上使用，通过**接口层**（而非 lake 依赖）连接。
- 优点：避开版本冲突。
- 缺点：接口层本身要证明**跨版本一致性**，且**无法在同一证明中使用两个库的定理**——这恰好否定了「复用」的主要收益。

### 5.5 须做的验证（不可跳过）

> **这是本路线唯一「不实测就无法决策」的工程风险。** 依 [`../04-文献与依赖/04-跨库版本对齐风险.md`](../04-文献与依赖/04-跨库版本对齐风险.md) 第五节，须做一次**多库 `lake` 依赖可行性验证**：
>
> 1. 建一个空的 Lean 项目，固定 `v4.33.0`（Causalean 版本）。
> 2. 尝试加入 Causalean，`lake build` 看是否通过。
> 3. 尝试加入 SLT 库（`v4.32.0`），看报什么错、错多少。
> 4. 记录精确的失败清单。
> 5. 换 `v4.32.0` / `v4.35.0-rc4` 各重做一遍。
>
> **产出应是一张「版本 × 库」可行性矩阵，而不是估计。**

### 5.6 本机环境的实测报告（**可以做本地构建验证**）

本次写作对本机环境做了直接实测：

| 项 | 实测结果 | 命令 |
|---|---|---|
| `lean` | **已安装**，`Lean (version 4.14.0, x86_64-w64-windows-gnu, commit 410fab728470, Release)` | `lean --version` |
| `lake` | **已安装**，`Lake version 5.0.0-410fab7 (Lean version 4.14.0)` | `lake --version` |
| `elan` | **已安装**，`elan 4.2.3 (b6cec7e10 2026-06-08)` | `elan --version` |
| 已装工具链 | `leanprover/lean4:v4.14.0`（默认）、`leanprover/lean4:v4.33.0-rc1` | `elan toolchain list` |

**三条直接推论**：

1. **本路线具备本地构建验证能力——这是把本文件中一切「假设」变为「事实」的唯一途径。** 第二节中四处 `[需进一步核实]`、第三节中四个「待审」依赖、第四节与裁决 C 的冲突（Q-C1／Q-C2／Q-C3），**全部可以而且应当用本机实测闭环**。
2. **但本机已装的两条工具链与本路线需要的不完全对齐**：已装的是 `v4.14.0` 与 `v4.33.0-rc1`，而需要的是 `v4.32.0`（SLT/FoML）、`v4.33.0`（Causalean）、`v4.35.0-rc4`（Mathlib master）。**`v4.33.0-rc1` 是 `v4.33.0` 的候选版，不等于 `v4.33.0`**——用它构建 Causalean 属于「近似对齐」，其失败清单**不能直接当作正式结论**。故第五节的验证须先用 `elan` 拉取精确版本。
3. **构建前的必要准备（依 Causalean README 与审查记录）**：须先 `lake exe cache get` 拉 Mathlib oleans，否则要编译数小时；Causalean 另有预编译 oleans 的获取脚本。**Windows 注意**：README 要求用 **Git Bash**（非 PowerShell），需 `zstd` 在 PATH，建议 `git config --global core.longpaths true`。**仓库约 112 MB，本次审查记录到 `RPC failed; curl 18 transfer closed` 的网络失败，需重试；`--filter=blob:none` 可成功但 checkout 极慢。**

---

## 六、准入门槛（新章节）

依**作者裁决 G** 第 1、3 条（「用，但要检查」「所有外部依赖库需要进行对抗性审查」）与对抗审查的建议，**本路线在采用任何外部依赖之前，必须通过以下五道门槛。未通过者不得出现在证明中**（承裁决 G 第五节「无登记的依赖不得出现在证明中」）。

### 门槛 1：`lake build` 通过

**为什么必要**：**「源码树无 `sorry`／`axiom`」≠「该 commit 能构建」。** 对抗审查与独立复核均明确声明**自己没有运行 `lake build`**，因此其全部「0 命中」都是**文本 grep 的结果，不是编译验证的结果**。独立复核记录第三节逐字：「我的复核能确认的是：**文本层面** Discovery 簇不含结构学习算法的记号；我的复核**不能**确认的是：库是否真的编译通过、是否真的 sorry-free。」

**操作**：pin 到确切 commit → `lake exe cache get` → 拉上游预编译 oleans（若有）→ `lake build`。**记录完整输出与失败清单。**

### 门槛 2：`#print axioms` 检查（无 `sorryAx`）

**为什么必要**：机械扫描查不出**通过别的途径引入的可信假设**——例如 Mathlib 上游的公理、或 `native_decide` 已编译进 olean 的情形。**这是「用公理冒充证明」这一类失败的唯一权威检出手段。**

**操作**（对**本路线实际引用的每一条**定理，而非抽样）：

```lean
import Causalean.Graph.DAG
import Causalean.SCM.ID.Backdoor

#print axioms Causalean.SCM.globalMarkov
#print axioms Causalean.SCM.backdoor_identifiable_ae
#print axioms Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk
```

**判定标准**：
- **预期**：只输出 `propext`、`Classical.choice`、`Quot.sound`（Lean 标准三公理）。
- 若出现 `Lean.ofReduceBool` / `Lean.trustCompiler` → 该定理依赖 `native_decide` 的编译产物公理，**可信度降低到「信任 Lean 编译器」而非「信任内核」**。
- 若出现任何**自定义 `axiom` 名** → **该定理不可用**。

**本项对 Causalean 有特殊意义**：论文 v1/v4 称「只有 `native_decide` 的编译产物公理」，而审查与复核**在全部已扫文件中 `native_decide` 0 命中**。**倾向已被消除，但未能穷尽确认**——因为未对全部 2,621 个 `.lean` 做穷尽扫描（网络分块拉取超时）。**不自己跑 `#print axioms` 就无法定论。**

### 门槛 3：机械扫描禁用记号

**为什么必要**：这是**最低成本、最高收益**的一道。Causalean 自己把禁用集合定为 `axiom`／`sorry`／`admit`／`native_decide`／`opaque`／`unsafe`——**比一般实践更严（含 `opaque` 与 `unsafe`）**，值得照用。

```bash
git grep -n -w sorry -- 'Causalean/*'
git grep -n -E '^\s*(noncomputable\s+)?(private\s+|protected\s+)?axiom\s' -- 'Causalean/*'
git grep -n native_decide -- 'Causalean/*'
git grep -n -E '^\s*unsafe\s' -- 'Causalean/*'
git grep -n -E '^\s*(noncomputable\s+)?(private\s+)?opaque\s' -- 'Causalean/*'
```

**并将门槛 2 与门槛 3 的断言纳入 CI**：一旦上游更新导致公理集变化，立即报警（依对抗审查步骤 E）。

### 门槛 4：声明级比对（「声称覆盖什么」vs「实际覆盖什么」）

**为什么必要**：对抗审查最有价值的发现（Discovery 簇的预期差）**恰恰是读论文摘要读不出来的**。论文称为「discovery」的簇，实际是**识别理论，零算法覆盖**。依赖审查**必须落到代码/声明层，不能停在摘要层**。

**操作**（四步，按成本从低到高）：

1. **下载机器可读清单**：`https://causalsmith.org/library/search.json`（13.3 MB，**15,821 条**记录，字段：`n`=全名, `k`=种类, `m`=模块, `a`=簇, `t`=tier, `d`=docstring 译文, `s`=**Lean 类型签名**, `l`=行号, `f`=文件路径）。**注意：引用 Causalean 时不能照抄论文里的声明名**——论文 v4 Table 3 的 `frontdoor_identifiable_ae` **按此名在仓库中不存在**（实为 PO 侧 `ate_frontdoor` 与 SCM 侧 `frontdoor_adjustment_ae`）；13 个抽查名中 **12 个逐字命中、1 个重命名**。
2. **读每条声明的 Lean 类型签名**（`search.json` 的 `s` 字段）——**可以完全不采信其自然语言译文**，直接看形式化陈述。
3. **不看译文，自己把签名逐字读一遍**，确认：假设是否够用？结论是否就是我们要的？是否有**空洞假设**（如 `True`）？是否有**未被使用的假设**（漏掉前提的常见信号）？**特别检查**：是否有 `hNonempty` 之类的非空性守卫、是否有 `=ᵐ[...]` 而非 `=`、前提是否被库标注为「比经典版更强」。
4. **记录到 `proof/03-假设登记.md`**。

**为什么第 3 步不可省**：库自承其 statement audit **由 LLM 执行，且作者明确未估计错误率**（v4 §7 逐字："the statement-match audit is itself an LLM task… **we do not estimate how often they err**"）。**它的审计结论对我们是不可继承的——继承就等于把「LLM 审计 LLM」的不可靠链引入我们的信任基。**

### 门槛 5：pin 到确切 commit

**为什么必要**：Causalean 的规模在半年内由 **7,035 → 8,179 → 15,821**（站点索引 commit `2adec37`）。**规模翻倍以上。** 且 README 提到「**one name per result**」的重命名工作——**声明名可能被重命名或移除**（已兑现实例：论文 Table 3 的 `frontdoor_identifiable_ae`）。

**操作**：
- 在 `lakefile.toml` 中用 `rev = "…"` 而非 `main`。已记录的可用 pin：仓库 HEAD `47acf19565b6c280f0f515fcf1f11f26324381c6`（2026-10-07）；站点索引 commit `2adec37c6afdd6e4969acdf5b5884fbfae4f5617`。
- **同时 pin Mathlib rev**：Causalean 的 `db584cd6d46c92f209a44c0f1c829460d327499d`。
- 记录 `lake-manifest.json` 的 hash → 任何时刻可复现同一环境。

### 6.1 准入门槛的适用对象与顺序

| 门槛 | 适用对象 | 通过后得到什么 |
|---|---|---|
| 1 | **每个**外部依赖 + **vendored 依赖** | 「该 commit 可构建」这一事实 |
| 2 | 本路线**实际引用的每一条**定理 | 「该定理不依赖非标准公理」这一事实 |
| 3 | **每个**外部依赖全库 | 「无禁用记号」这一**文本层**事实 |
| 4 | 本路线**实际引用的每一条**声明 | 「该声明的形式陈述就是我们要的命题」这一判断 |
| 5 | **每个**外部依赖 + Mathlib | 「环境可复现」这一事实 |

**一条顺序纪律**：**门槛 1 与 2 必须在门槛 4 之前完成。** 理由：若库根本不能构建，则对其 15,821 条声明做逐条陈述审查是纯浪费。

---

## 七、成本估计（保留诚实处理）

### 7.1 原文的 5–10 年不可采信（保留旧版全部理由）

原文（`（过程产物，不在成品集内）`）给出：

> 「形式化 do-calculus 可能 1-2 年。形式化 SCM 可能 1-2 年。形式化因果发现可识别性可能 2-3 年。形式化规则学习泛化界可能 1-2 年。总计：5-10 年，还不一定成。」

**该组数字不可采信，理由三条，逐条独立、可逐字核对：**

**第一条：该轮无任何检索行为。** 该段位于第 23 轮（`F-工程实现.md:1556` 起为第 23 轮），该轮**未出现任何检索、查询或引用外部资料的行为**；其「已有的／没有的」清单（该文件 `:1632–1651`）是模型自述，无出处标注。**一份没有经过任何核实的成本估计，其数字的来源只能是语言模型的先验——这不是估计，是生成。**

**第二条：数字加不起来。** 四项区间为 $[1,2]$、$[1,2]$、$[2,3]$、$[1,2]$。**区间加法的规则是端点相加**：下界 $1+1+2+1=5$，上界 $2+2+3+2=9$。故这四项之和的区间是 $[5,9]$，而原文写「总计：5-10 年」。**上界 10 与 9 不符**，多出的 1 年无来源。这说明「总计」不是由分项加出来的。

**第三条：下一轮作者自己推翻。** `00-总纲.md` 第二节「另两处修正」第 2 条已登记：「**下一轮作者自己推翻**（第 24 轮做了检索后结论改变）。」

**第四条（本次新增，且是该判断最强的确认）**：**该数字的偏差方向已被本次实测定位——它偏高，且偏高是可证实的。** 原文的四项分项中，「形式化 SCM」与「形式化因果发现可识别性」两项**已有 Causalean 的现成实现**（15,821 条机器检验声明），「规则学习泛化界」中的**泛化界一侧**（Rademacher 复杂度）**已有 FoML 与 lean-stat-learning-theory 两个成熟库**。**四项中至少有二项半的「从零建」前提已不成立。** 这不再只是「缺少依据」，而是**依据已出现且与之相反**。

**综合**：四条理由中任意一条都足以使该组数字不可采信；四条同时成立时，该组数字**不具备任何信息量**。本文件据此**不复述、不修正、不继承**该组数字。

### 7.2 本文件不给新的年数

**本文件同样不给年数。** 理由与判断原文数字不可采信的理由**是同一条**：在**没有做过形式化、没有通过第六节准入门槛、没有对任何一条定理做过原型**的条件下，任何具体的年数都是**生成而非估计**。给定年数会造成三种伤害：

1. **它会被当作计划输入。** 一旦写出「`Rules` 约 2 年」，排期、人力与验收标准就会以 2 年为基准建立；而该数字的实际不确定性横跨一到两个数量级。
2. **它掩盖了真正决定成本的因素。** 决定成本的不是「有多少条定理」，而是「是否存在卡住的地方」（见 7.3 与 7.4）。前者可估，后者不可估。
3. **它与本文件自身的证据政策冲突。** 本文件对现状的判断都标了证据强度，却对工期给确定数字，这在方法论上不自洽。

**改用「相对量级 + 已知难点」**：把「要花多久」替换为「会卡在哪里」。后者是可核查的，前者不是。

### 7.3 成本图景比旧版乐观（**本次新增的核心更新**）

**这是一处方向明确的更新：因可复用性大幅提高，成本图景整体比旧版乐观。** 三条具体理由：

1. **因果层的从零建部分整体消失。** 旧版的 8 个 `Causality.*` 库中，**4 个整体复用、3 个需适配后复用**。旧版为这 8 个库分配的「小项目 1／小到中等 1／中等 3／大项目 3」的量级，**其中约 60–70% 被复用吸收**（此 60–70% 为对抗审查给出的估计，标 `[调研代理报告]`；本文件不把它当作精确数字使用，只用于说明**方向**）。
2. **随机分析层的从零建部分整体消失。** 旧版的 `Stochastic` 为「大项目到研究级」，其八组内容中**布朗运动、鞅收敛两组整体复用 Mathlib**（实测文档页），**Itô 组跟进上游**，**SDE 组的证明工具（Grönwall、Picard–Lindelöf）复用 Mathlib**。**残余自建部分只有 SDE 本体、Fokker–Planck、马尔可夫链遍历性、Euler–Maruyama 离散化四项。**
3. **误差界/泛化界层的从零建部分整体消失。** 旧版把「规则学习泛化界」列为研究级。**其中「泛化界」一侧（Rademacher 复杂度、集中不等式、Dudley 熵积分、VC）已有两个成熟库**。真正仍是研究级的，只剩**「规则空间的泛化界」**这一支——因为 $\mathcal{R}$ 是**离散结构空间**而非函数空间，标准 VC/Rademacher 理论不直接适用（这一判断**未被本次调研推翻**：缺口复用调研第五节第 5 条明写「『规则空间泛化界』的形式化 —— 未查到」）。

**但须同时写明四条反方向的成本，以免本节的乐观被过度外推**：

1. **复用不等于零成本。** 复用一个 15,821 条声明的库，其成本在**读懂、审查、适配**三处，而非在抄写。
2. **旁路不等于不做。** 依裁决 C「不降级、不移出、不暂缓」，因果层虽走旁路（`00-总纲.md` 第二节裁决 A），**仍是必做**——只是不做承重项。
3. **规模分布反而更「重」了。** 见 4.3：6 个库中大项目 4 个（含叠加）、研究级 1 个。**数量减少了，但剩下的恰是难的**——因为好做的都被复用了。**这不是坏消息，但必须如实说。**
4. **新增了一条旧版没有的、可阻塞整条路线的成本：版本对齐。** 见第五节。

### 7.4 新的成本来源（**本次新增**）

旧版的成本来源是「自建库」。**本次实测显示，主要成本来源已经转移**——复用的收益必须用以下四项新成本来支付：

| # | 新成本来源 | 内容 | 与旧版的差异 |
|---|---|---|---|
| **1** | **版本适配** | 三块库锚在三个不同 Lean 版本上（落差最大 3 个 minor），**不能同时作 lake 依赖**。适配包含：选版本、移植、或建接口层 | **旧版完全没有此项。** 旧版假定「自建库跟随 Mathlib」，没有第三方版本约束 |
| **2** | **依赖审查** | 依裁决 G 与第六节：每个依赖须过五道门槛，vendored 依赖（FoML、optlib）须各自建档。**审查是逐条声明的，不是抽样的** | **旧版完全没有此项。** 旧版无外部依赖，故无审查成本 |
| **3** | **接口层（适配性命题）** | `01-定理清单.md` 的 **T9.1–T9.9** 共 9 条适配性命题。**外部结果不能直接搬用**——每条被引用时须先证「它说的是不是我这里的这个对象」 | **旧版已正确识别此项**（T9.x 层），但旧版把它算作「引用外部文献的适配成本」；**现在它的对象变成了具体的 Lean 库**，故须**逐条落到声明**（核对 Causalean 的 `dSep` 内建不相交性、`=ᵐ[...]` 而非 `=`、`hNonempty` 守卫等） |
| **4** | **上游漂移的持续成本** | 半年内 7,035 → 8,179 → 15,821；已有「one name per result」重命名；Mathlib 侧的改名实例（`tendsto_of_uncrossing_lt_top` → `tendsto_of_upcrossings_lt_top`，2026-09-17 deprecated） | **旧版列为「未知难」第 (4) 项（Lean 版本耦合），一笔带过。** 现在它有精确的数字与已兑现实例 |

### 7.5 已知难的地方（更新）

**（1）`Rules` 的泛化层——全表最重的一处，判为研究级。** 困难不在工作量，而在**载体不匹配**：

- 标准泛化理论（VC、Rademacher、覆盖数）以**函数空间**为对象，而 $\mathcal{R}$ 是**离散结构空间**（规则集）。
- **已实测的两个成熟库均不覆盖此情形**：FoML 与 `lean-stat-learning-theory` 的对象是函数类；Causalean 自己的 `Stat/Concentration/` 也建立在函数类上。
- **唯一可行的绕行**（承 `04-误差界路线.md` $\textsf{E}_2'$）：若承认有限 $\epsilon$-覆盖，则退化为有限类集中不等式——**此路径可证**；否则须建立新理论。
- **前件「规则长度一致有界」未定**（`03-假设登记.md` E16，标为「经验假设（候选）」）。

**（2）`Discretization` 的「连续 → 二值编码」误差界。** 判为**大项目**（非研究级，理由：属初等分析）。困难：

- **实测确认为真空白**——FloatLib 管算术、Grönwall 管 ODE 扰动、Coq/Isabelle 提供范式，**但「把连续对象编码成二值」这一步的误差界无任何形式化**。
- **须从零定义** $\mathrm{enc}$／$\mathrm{dec}$／二值化方案与阈值非退化条件。
- **可借的现成设施只有一处**：`Mathlib.Analysis.ODE.Gronwall` 的 `dist_le_of_approx_trajectories_ODE`（**实测文档页确认**）——它给出「近似解与真解距离 ≤ `gronwallBound δ K (εf + εg) (t - a)`」，正是数值方法离散化误差分析的核心工具。

**（3）`Causality.IDCompletion` 的完备性方向。** 判为**大项目**（非研究级，理由：Pearl 的 ID 完备性与 hedge 判据在文献中已有成形证明可转写）。困难三层：

- **第一层：表达式的语法。** 须先把「含 $do(\cdot)$ 的干预表达式」语法化，定义子代换与「一个表达式在模型中的值」。纯语法工作，工作量大但**不难**。
- **第二层：规则的可施用性判定。** 三条规则各带一个图条件。判定该条件需要 d-分离的**可判定性**——**这一层可直接复用 Causalean**（`dSep` 定义为 Bayes-Ball 可达，且 `bbReachableVertices_iff_activeWalk` 已证其与活跃路径等价）。**这是本次实测带来的实质成本下降。**
- **第三层：完备性本身。** 须构造「典范模型」或给出 ID 算法族并证其完备。**形式化这一证明不是「把已有的证明翻译成 Lean」，而是要先把证明的每一步在 Lean 的类型中重新组织。**

**（4）与裁决 C 的冲突项（Q-C1）本身构成一处成本不确定性。** 若裁决 C 原文不变（自建随机分析库），则成本为**重写 Mathlib 已有的布朗运动与鞅论**；若采纳本文件建议（复用 + 补缺口），则成本为**版本适配 + 接口层 + 四项真缺口**。**两条路径的成本结构完全不同，且这条分叉未决。** 这是本文件登记的最重要的一处**决策性**成本不确定。

### 7.6 未知难的地方（更新）

**（1）版本矩阵的实际失败规模。** 第五节的验证尚未做。**「移植一个差 2 个 minor 的 Lean 库需要多少工作量」未实测**——（跨库版本对齐风险 §六逐字：**不应给数字**）。这个未知是**可消除的**（本机已具备条件），且**消除它的优先级最高**——因为它决定 `lakefile.toml` 的第一行。

**（2）`Rules` 泛化层的「是否存在关键技术手段」。** 若有限 $\epsilon$-覆盖不成立，则须建立离散结构空间上的新复杂度理论。**其完成不取决于工作量投入，而取决于是否出现关键的新技术手段。** 这一判断 `[推断]`，依据是「该方向在任意证明助手中零形式化」这一事实。

**（3）条件分布的正则版本。** 因果推断的几乎所有公式都写成 $P(Y\mid X=x,Z=z)$ 形式。**本项未在本次调研中被正面核实**——缺口复用调研第五节第 10 条逐字：「**Causalean 中 `Causality.CondIndep`、`Causality.Counterfactual` 的确切覆盖** ——……**未能逐一声明核对**这两个具体概念的实现细节」。**但间接证据较强**：Causalean 的 `obsCondKernel`（`Model/Kernel.lean:244`）是**派生**的，且依赖-Causalean 记录其 `SCM` 要求 `StandardBorelSpace` 等测度论正则性 instance。**故本项由旧版的「未知难」降为「待核实的中等风险」，但未消除**：若本框架需要相交集合的 d-分离（`dSep` 内建不相交性所禁止）或病态空间，本族全部公式仍须重写。**波及范围覆盖 `Identification`、`DoCalculus`、`Counterfactual` 三库。**

**（4）Causalean 的双框架（SCM vs PO）不自动桥接。** 见 3.3。若本路线不先固定权威记号，会积累未被证明的隐含假设——**这正是内核查不出的那类错误**。

---

## 八、风险登记（更新）

| # | 风险 | 性质 | 后果 | 应对 |
|---|---|---|---|---|
| **R-版本** | **跨库版本冲突** | **阻塞级** | Mathlib master `v4.35.0-rc4`、Causalean `v4.33.0`、SLT／FoML `v4.32.0` **不能同时作 lake 依赖**。选任一个都意味着放弃另两块，或自行移植 | **优先级最高**。执行第五节的「版本 × 库」可行性矩阵；**产出矩阵之前不得冻结 `lakefile.toml`** |
| **R-Discovery** | **预期差（内核查不出的缺失）** | **最高** | 以为 Causalean 的 `Discovery` 簇覆盖「因果发现算法」，从而不自建——**实际该簇零算法覆盖**（PC／GES／FCI／CPDAG／Meek 全 0，三个非零命中均为假阳性）。**后果是我们在完全不自知的情况下缺失整块能力** | ① 本文件第二节已把该项标为「真空白」；② **`Causality.Discovery` 库降级为「参考」，不作复用对象**；③ 若确需结构学习算法，**须自建**（但依 `00-总纲.md` 裁决 A 因果走旁路，其优先级由作者裁决） |
| **R-同名不同义** | **`hedge`／`Lyapunov`／`stochasticIntegral`／`GES`／`dSep`／`MarkovEquiv` 陷阱** | 高 | 用 grep 检索会得到**完全错误的印象**；`Lyapunov` 会命中一个**完全不相关的 CLT 矩条件**；`dSep` 会对相交集合**类型上直接失败** | **禁止以 grep 命中作为覆盖度证据**（这是 3.4 节存在的理由）。所有覆盖度判定**必须落到声明清单**（`search.json` 或 `decls2.tsv`） |
| **R-漂移** | **上游半年内 3 次规模改动 + 改名** | 中高 | 7,035 → 8,179 → **15,821**；已有「one name per result」重命名（论文 Table 3 的 `frontdoor_identifiable_ae` **按此名不存在**）；Mathlib 侧亦有改名实例。**不 pin commit 会导致证明反复失效** | **准入门槛 5**（pin 到确切 commit + 记录 `lake-manifest.json` hash）；把门槛 2、3 的断言纳入 CI |
| **R-vendored** | **依赖的依赖未被审查** | 中高 | Causalean 携带两个 in-tree vendored 依赖（**FoML**、**optlib**）。**in-tree 副本可能被修改、可能不跟随上游**；若本路线另直接依赖上游 FoML，则「直接依赖」与「vendored 副本」是**两份不同代码** | **须各自单独建档**（依裁决 G 第 2 条）；核对 in-tree 副本与上游的差异（`UPSTREAM.md`）；**in-tree 副本的认证等级不能高于上游本身** |
| **R-审查继承** | **继承 Causalean 的 LLM 审计结论** | 中高 | 库自承其 statement audit **由 LLM 执行且未估计错误率**（v4 §7 逐字）。**继承 = 把「LLM 审计 LLM」的不可靠链引入我们的信任基**。已发现的真实例证：`OracleInequality.lean:95` 的 `TODO(faithfulness)` 存在「系数 4/σ vs 正文 2/σ」不一致 | **机械层照用（门槛 2、3）；语义层由人类逐条签署**（准入门槛 4 第 3 步）。我们体量小，负担得起 |
| **R-假设不匹配** | **Causalean 的假设体系与本框架不匹配** | 中高 | 该库的 `SCM` 要求**潜变量根相互独立**（由乘积测度自动给出）；若本框架允许潜变量相关，则 `globalMarkov`、do-calculus、backdoor **全部不适用**。该库还要求 `StandardBorelSpace`／`Nonempty` 等正则性；其 ID 可靠性定理带 `hNonempty : ∃ M, ...` 守卫**专门用来排除空模型类上的空洞全称量化**——**我们若自己构造 instance 也可能重新引入** | **这是内核查不出的那类错误**（表面成立、实质错误）→ 落入准入门槛 4 与 `01-定理清单.md` 的 T9.x 适配层 |
| **R-双框架** | **SCM 与 PO 两套框架并存且不自动桥接** | 中高 | 若不先固定权威记号，会积累**未被证明的隐含假设**（误用风险 M7） | 见 3.3：**先在本路线内选定权威记号并在定理清单上标注** |
| **R-ID误用** | **把「ID 有可靠性」误读为「ID 可用」** | 中高 | `idAlgorithm` 返回 `false` **不带任何不可识别性声明**（`Checker.lean:191` 附近逐字："A `false` result carries no nonidentifiability or hedge claim"），且 `idSucceeds` 自称 **no-additional-fixing 近似**。基于它下结论会产出**无依据的不可识别性断言** | 引用时**必须**在定理陈述中带上「仅可靠性方向」这一限定；缺口以新立的 `Causality.IDCompletion` 承接 |
| **R-浮点** | **FloatLib 的仓库位置未定位** | 中 | 浮点误差是本路线 E2 类误差的来源之一（对应 `Equivalence` 的浮点偏差条款）；**若该库不可获取，则该项无外部支撑** | 依裁决 G 第 3 条**先做对抗审查**；**核实前视同无现成库** |
| **R-Lyapunov** | **控制论库的仓库 URL 未确认** | 中 | 文献索引逐字：「具体 URL 未在正文中直接给出，**未确认**」；且 `forgi86/control-theory-in-lean` 与该库的关系**未确认** | **核实前按「无可用库」处理**；若须 Lyapunov 稳定性，先定位仓库并过五道门槛 |
| **R-裁决冲突** | **本文件建议与裁决 C 冲突（Q-C1）** | 中（但性质是决策性） | 若照裁决 C 原文执行「自建随机分析库」，实际含义是**重写 Mathlib 已有的布朗运动与鞅论**——工程负收益，且与裁决 G 第 4 条冲突 | **标为待作者裁决**（Q-C1／Q-C2／Q-C3）。本文件不擅自推翻裁决 C |
| **R-两栏误读** | **把「原则上可形式化」当作「已有」** | 方法论 | 工作量级被低估一个档位以上 | 强制执行第二节的**三栏**表；任何安排工作量处必须引用**第二、三栏**而非第一栏 |
| **R-第三栏误读**（新增） | **把「有现成库」当作「可直接依赖」** | 方法论 | 未经审查的依赖进入信任基；**旧版恰好犯了反向的错（把「不在 Mathlib」当作「必须自建」）** | 第三栏非空≠可依赖。**准入门槛六个字：不跑不采信。** |
| **R-成本数字复发** | **再次出现不可采信的成本数字** | 方法论 | 与原文第 23 轮同类的错误重现 | 本文件第七节已给出四条判据（无检索／加不起来／被下一轮自我推翻／**偏差方向已被实测定位**）；后续文件对成本数字一律适用同一判据 |

---

## 九、结论

**结论 1（范围，本次重估的核心）**：**自建库由 13 个减至 6 个。** 清单为：`Rules`、`Fate`、**`Discretization`（新立）**、**`Causality.IDCompletion`（新立）**、`FCA`（暂缓）、`Equivalence`。其中**建议优先开工 2 个**：`Discretization` 与 `Rules`——理由分别是：`Discretization` 是实测确认为真空白的唯一一处（无任何可复用替代），且是 `Rules` 编码算子层的硬前置；`Rules` 是主链（实例 → 规则 → 预测）的起点，其 $\alpha$ 的存在性已由 FCA 基本定理保证（裁决 D），故**规则层不再有存在性缺口**。

**结论 2（规模分布，依实测重估）**：6 个库中，**小项目 1 个**（`Fate` 定义层）、**中等项目 2 个**（`Rules` 定义层、`Fate` 存在性层）、**大项目 4 个**（`Rules` 语义层、`Discretization`、`Causality.IDCompletion`、`Equivalence`）、**研究级 1 个**（`Rules` 泛化层）、**暂缓 1 个**（`FCA`）。**相比旧版 13 个库（大项目及其以上约占二分之一），数量减半但难度分布的「重心」反而上移——因为好做的部分已被复用吸收。** 这不是坏消息，但必须如实说。

**结论 3（Mathlib 缺口的最小集）**：本路线**必须自建**的部分是：**`Rules` 的语义层与泛化层**（规则空间的代数结构、γ 判据、∘ 语义、离散结构空间上的泛化界）、**`Fate` 的本理论特有定义**、**`Discretization` 全库**、**`Causality.IDCompletion` 的四项补缺**（ID 完备性、hedge 证书、R2/R3 完整图形一般性、嵌套反事实）、**`Equivalence` 的目标语言语义层**。

**「Mathlib 缺因果推断」这一判断**——**至今成立，且性质不变**：不是「正在补的缺口」，而是「不在其选题范围内」。**但它的工程后果在本次调研后被改写**：旧版由此推出「必须自建 `Causality.*` 全族」；**实测显示该缺口已由一个独立的第三方库（Causalean）填充**，故正确的推论是「**必须依赖第三方，不能等上游（Mathlib）**」——自建库是固定资产这一说法，**只对 `Rules`／`Fate`／`Discretization`／`Equivalence` 成立**。

**结论 4（与裁决 C 的冲突，如实报告）**：裁决 C 命令「**自建随机分析库，连续情形全量形式化**」。**本文件实测显示：布朗运动（`IsBrownianReal`／`IsPreBrownianReal`）、鞅收敛（Doob 全套）、ODE/Grönwall 均已在 Mathlib 主线**；Itô 积分虽 Mathlib 无（实测 404），但上游 `RemyDegenne/brownian-motion` 正在建。**故本文件建议将连续情形的处置由「自建」改为「复用 + 补缺口」（Q-C1），并标为待作者裁决。** 本文件**不擅自推翻裁决 C**，并明确声明：**该建议不构成「降级」**（裁决 C 撤销的是「降级为登记」，本建议仍要求**全量形式化**，只是方式不同），**也不减少任何必做条**（T5.2／T5.10／T5.11／T5.16 仍全部为必做）。

**结论 5（成本处理）**：本文件**不给年数**。原文的 5–10 年因四条理由（无检索、加不起来、被下一轮自我推翻、**偏差方向已被实测定位**）不可采信。**成本图景整体比旧版乐观**（因果层 8 库中 7 库复用、随机分析层八组中三组复用、泛化界一侧有两个成熟库），**但新增四类成本**：版本适配、依赖审查、接口层（T9.x）、上游漂移。**结论是：主要成本来源已经从「自建库」转移到「复用与适配」——成本结构变了，不是成本消失了。**

**结论 6（准入门槛是唯一能把「假设」变「事实」的手段）**：本文件第二节有 **4 处 `[需进一步核实]`**、第三节有 **4 个「待审」依赖**、第四节有 **1 处与最高优先级裁决的冲突**。**这三类问题全部可以通过本机实测闭环**——`lean`／`lake`／`elan` 均已安装（实测），唯一缺的是用 `elan` 拉取精确版本（需 `v4.32.0`／`v4.33.0`／`v4.35.0-rc4`，本机现有的是 `v4.14.0` 与 `v4.33.0-rc1`）。**因此本文件的首要后续动作不是写更多文档，而是执行第六节的五道门槛与第五节的版本可行性矩阵。**

---

## 十、依判决 C 与后续调研的重写记录

> **本节地位**：记录本次**完整重写**改了什么、依据什么、哪些与裁决 C 冲突待裁决。**上一版的「附二、依作者裁决 C 的修订记录」共 21 处修订，本次重写不是在其上追加，而是整体重做**——因为上一版的事实基础已被推翻，追加式修订无法承载。

### 10.1 重写的触发原因：上一版被实测推翻的判断

| # | 上一版的表述 | 实测结果 | 判定 |
|---|---|---|---|
| 1 | 「**自建随机分析库**」（§3.1 序 12、§3.2.12 整节；内容含布朗运动构造、独立增量、高斯性、二次变差、马尔可夫性、自相似、反射原理、无处可微） | **布朗运动已在 Mathlib 主线**（`IsBrownianReal`／`IsPreBrownianReal` 为**主定义**；独立增量、弱 Markov 性、协方差 `min s t`、尺度不变、反演不变、a.s. 连续路径**均有定理**）`[实测文档页]` | ❌ **推翻** |
| 2 | 鞅收敛「**不确定**」；「Doob 分解与收敛定理**不确定**」 | **Doob 鞅收敛全套已在 Mathlib**（`Submartingale.ae_tendsto_limitProcess`／`tendsto_eLpNorm_one_limitProcess`／`ae_eq_condExp_limitProcess`／`tendsto_ae_condExp`／`tendsto_eLpNorm_condExp`）`[实测文档页]` | ❌ **推翻** |
| 3 | ODE「**部分有**」；§4.3 第 (4) 条把马尔可夫链／鞅收敛列为「**依赖 Mathlib 的底层缺口**」「范围扩张的风险点」 | **`Mathlib.Analysis.ODE.Gronwall` 完整**（含 `dist_le_of_approx_trajectories_ODE`——数值方法离散化误差分析的核心工具）`[实测文档页]` | ❌ **低估** |
| 4 | 「统计学习理论**只是一个线索**」（旧版 §二「信息论／凸优化」一带而过，从未把 SLT 作为可复用项） | **两个成熟库**（FoML／ITP 2026；lean-stat-learning-theory／ICML 2026），**且已被 Causalean 复用**（`ML/` 簇 uses FoML，FoML 以 in-tree vendored 形式存在并被 `Stat/Concentration/`、`Estimation/`、`ML/` 消费） | ❌ **严重低估** |
| 5 | Lyapunov／动力系统「**须自建**」（§3.2 Dynamics「依赖 Mathlib 的 SDE/马尔可夫链部分（覆盖**待核验**）」） | **已有 Lean 控制论库**（Doll & Shames，arXiv:2607.19727，2026-07），含 Lyapunov 定理、LaSalle、不变集、小增益定理 | ❌ **推翻**，但**仓库 URL 未确认** |
| 6 | **完全不知道 Causalean 的存在**（旧版全文无「Causalean」「CausalForge」「CausalSmith」字样） | **Causalean 是真实、可用、机器检验的因果推断 Lean 4 库**：15,821 条声明／2,616 文件／~589,000 行；`sorry`／`axiom`／`native_decide`／`admit` 战术**全 0 命中**（三个独立审计 × 全簇） | ❌ **重大遗漏** |
| 7 | 「`Causality.*` 全族**须自建**」（序 1–8，共 8 个库） | **实测 18 项覆盖度比对：✅ 9 ／ ◐ 4 ／ ❌ 5**。原 11 库中 **3 个可原样复用、4 个需适配后复用、1 个降级为参考、3 个仍需自建** | ❌ **重大修正** |
| 8 | §二 表格**只有两栏** | **两栏不足以支撑工作量判断**——「Mathlib 无」≠「必须自建」。**强制改为三栏** | ⚠️ **结构性缺陷** |
| 9 | 本文件对 Mathlib 现状的全部判断标 `[基于既有知识·未核验]` | **本文件此后全部标注四档证据强度**（`[实测文档页]`／`[实测仓库文件]`／`[调研代理报告]`／`[需进一步核实]`） | ⚠️ **方法升级** |
| 10 | 旧版假定「自建库跟随最新 Mathlib」，**无第三方版本约束** | **四个库锚在四个不同 Lean 版本上**（`v4.32.0`／`v4.33.0`／`v4.35.0-rc4`），**不能同时作 lake 依赖** | ⚠️ **新增阻塞项** |

### 10.2 本次重写对裁决 C 的执行与偏离（逐条对照）

| 裁决 C 的要求 | 本文件的执行 | 是否偏离 |
|---|---|---|
| 「不降级、不移出、不暂缓。凡能做的，一律做到底」（§一） | **全部保留**：`Equivalence` 仍立项（大项目）；`Rules`／`Fate` 不标「空壳」；`Causality.Discovery` 在本文件中的处置是「降级为**参考**」（即不再作为**复用对象**） | ⚠️ **部分偏离，须裁决**——见 10.3 冲突 4（该偏离不是撤销裁决 C，而是纠正一处**事实性错误**） |
| 「**自建随机分析库**，连续情形全量形式化」（§一表第 3 行） | **本文件建议改为「复用 + 补缺口」**（Q-C1），并标为**待作者裁决**。**「连续情形全量形式化」这一要求本身保留** | ❌ **偏离，已如实报告** |
| 「`Rules`／`Fate` 不再标空壳，改为『待理论补完后建』」（§一表第 4 行、§三） | **完整保留**：`Rules`／`Fate` 均不标空壳；其补法方向（$\alpha$／$\gamma$／$\circ$／$\mathfrak{C}$）已在 4.3 承接 | ✅ **一致** |
| 「$\alpha$ 具体化为 FCA 取概念过程，存在性由 FCA 基本定理保证」（裁决 D） | **完整保留**：`Rules` 库的内容栏明写 $\alpha$ 定义为取概念过程 | ✅ **一致** |
| 「误差主量纲＝决策损失」（裁决 E） | **完整保留**：`Discretization` 的误差界栏按决策损失为主量纲 | ✅ **一致** |
| 「A33／A34 正式加入假设总账」（裁决 F） | **完整保留**：`Fate`／`Discretization` 的前件栏引用 A33／A34 | ✅ **一致** |
| 「成本评估按相对量级，并逐项标注依据」（§四第 4 条） | **完整保留并强化**：五档相对量级 + 每格一个「规模依据」列 | ✅ **一致** |
| 「难度评估仍不给年数」（§四第 2 条） | **完整保留**：第七节不给任何年数 | ✅ **一致** |
| 「凡未完成的，标为待证，不得因『最彻底』而把未证说成已证」（§四第 3 条） | **强化执行**：**本框架内已证者仍为 0 条**；全部复用项标注为「外部已有，本框架内未证」；新增四档证据强度标注 | ✅ **一致（加强）** |

### 10.3 与裁决 C 冲突的条目（**待作者裁决**）

**冲突 1（Q-C1）：连续情形的处置——「自建随机分析库」vs「复用 Mathlib + 跟进上游 + 补缺口」**

- **裁决 C 要求**：自建随机分析库，连续情形全量形式化（§一表第 3 行）。
- **裁决 C 作出时的事实基础**：本文件旧版把布朗运动标为「部分有（构造存在）；成套性质**不确定**」，把鞅收敛标为「**不确定**」，把 SDE 一行标为「**本表确定性最低的一行**……**明确标注：不确定。使用前必须实测**」。
- **实测推翻的**：布朗运动**已是 Mathlib 主定义且成套定理齐备**；Doob 鞅收敛**已在 Mathlib**；ODE/Grönwall **已在 Mathlib**。**唯一确实缺失的是 Itô 积分（实测 404）**，而它有活跃的上游开发线。
- **本文件的建议**：改为「复用 + 补缺口」（四步处置见 4.4 表）。**理由：照裁决 C 原文执行的实际含义是重写 Mathlib 已有的布朗运动与鞅论——工程负收益，且与同日期的裁决 G 第 4 条「一切能复用就复用」直接冲突。**
- **本文件同时声明的三条限定**（以免建议被误读）：① **不构成「降级」**（裁决 C 撤销的是「降级为登记」，本建议仍要求全量形式化）；② **不减少必做条**（T5.2／T5.10／T5.11／T5.16 仍为必做）；③ **生效前提是完成第六节准入门槛**——在 `lake build` 与 `#print axioms` 通过之前，「可复用」这一判断本身仍是假设。

**冲突 2（Q-C2）：`Stochastic` 是否仍作为独立库立项**

- **裁决 C 要求**：自建随机分析库正式纳入（§三）。旧版据此新立 `Stochastic`（序 12）。
- **本文件的建议**：**建议拆为两支**——复用部分**不立项**（布朗运动、鞅、鞅收敛、ODE/Grönwall 直接依赖 Mathlib）；**须自建部分**（SDE 存在唯一性、Fokker–Planck、马尔可夫链遍历性、Euler–Maruyama 离散化）**并入新立的 `Discretization` 与一个 `Stochastic.Gap`**。
- **理由**：立项的边界应当与「须自建的范围」一致，否则库名会掩盖「其实是在重写 Mathlib」这一事实。
- **若作者维持原裁决**：则 `Stochastic` 保留为独立库，但**须在其文档头写明「本库与 Mathlib 现有覆盖的重叠部分，是为裁决 C 的『全量形式化』要求而作，不是缺口填补」**——以免后续读者误以为 Mathlib 真的没有布朗运动。

**冲突 3（Q-C3）：`Fate` 存在性层的规模是否由「大项目」下调**

- **裁决 C 要求**：`Fate` 的**存在性层**（路径测度）**不再以空壳待之**——须在 `Stochastic` 库建成后**构造出路径测度**（旧版 §3.0 排列原则第 3 条）。
- **本文件的建议**：**路径测度的构造已不必自建**——实测确认 Mathlib 已有布朗运动与鞅收敛，`MeasureTheory` 已有乘积测度等设施。故 `Fate` 存在性层由「大项目」**下调为中等项目**（但**须先实测**：Kolmogorov 扩张定理与 Kolmogorov–Chentsov 连续性判据在 Mathlib 中的确切状态**本次未核实**）。

**冲突 4（非裁决 C，但同属待裁决）：`Causality.Discovery` 的处置**

- **裁决 C 要求**：「A-1 因果发现降级为条件定理」→ 按最彻底处理：**同时**做条件定理版与规格完备化尝试（§一表第 5 行）。旧版据此把 `Causality.Discovery` 的优先级由「中」上调为「高」，并说明「『因果发现降级为条件定理』这一处置依裁决 C 撤销」。
- **本次实测带来一个新事实**：Causalean 的 `Discovery` 簇**零结构学习算法覆盖**（PC／GES／FCI／CPDAG／Meek 全 0，三个非零命中均为假阳性，**经独立复核**）。
- **本文件的处置**：**把 `Causality.Discovery` 由「复用对象」降级为「参考」**——**这不是撤销裁决 C**（裁决 C 撤销的是「降级为条件定理」，而本文件撤销的是「复用 Causalean 的 Discovery 簇」这一**事实性错误**）。
- **但须提请作者注意的连带后果**：若本路线确需结构学习算法（A19「因果图已知」的确认需走完整个因果发现流程，见 `01-定理清单.md` §4.3 判据 2），则**该部分须自建，且它在裁决 C 下不得降级**。**本文件未为新自建项立项，因为该决策取决于作者对 A19 优先级的裁决。**

### 10.4 本次重写新增的章节与结构性变更

| 变更 | 依据 |
|---|---|
| **第二节现状核查表由两栏改为三栏**（新增「现成库（含链接）」「实测依据」「证据强度」） | 「Mathlib 无」≠「必须自建」；依裁决 G 第 4 条 |
| **新增第三节「依赖分层」** | 依裁决 G 第 2 条（所有外部依赖单独登记，标明用了什么、用来干什么）；含 L1／L2／vendored／仅参考四层，及 3.2 的 vendored 处置规则、3.3 的双框架风险、3.4 的六个同名不同义陷阱 |
| **新增第五节「跨库版本冲突」**（含 5.6 本机环境实测报告） | 整合 `ref/跨库版本对齐风险.md` 的实测数据；本机环境为本文件直接实测 |
| **新增第六节「准入门槛」**（五道门槛 + 适用对象与顺序） | 依裁决 G 第 1、3 条；对抗审查的明示建议（「`lake build` + `#print axioms` 不是可选项，是准入门槛」） |
| **第四节的库总数由 13 减至 6**，并**删除旧版 §3.2.1–3.2.13 的逐库详述**（因其中 7 个库的详述对象已是外部库，详述应属 `ref/依赖-Causalean.md` 而非本文件） | 复用后，逐库详述的位置应转移到依赖档案；**本文件只保留「自建什么、为什么、多大规模」** |
| **删除旧版第五节「FCA 的特别评估」**（原 5.1–5.4） | 依裁决 H，FCA **暂缓**；其评估待作者整理自有库后进行。**保留的唯一有效外部结论**已并入 4.3 的 `FCA` 行与第二节 |
| **新增第十节「重写记录」**，取代旧版「附二」（21 处修订） | 旧版是追加式修订；本次是整体重做，追加式记录无法承载 |
| **保留旧版的全部好内容**：§一「两栏原则」及其三种混栏误读分析（**强化为四种**）、§4.1 原文 5–10 年的三条批判（**新增第四条实测确认**） | 该部分经实测**未被推翻**，且是全文方法论的骨架 |

### 10.5 本文件的自我限界

1. **本文件对 Mathlib 的 `[实测文档页]` 判定共 4 处**（`Probability.BrownianMotion.Basic`、`Probability.Martingale.Convergence`、`Analysis.ODE.Gronwall` 三页 HTTP 200，`Probability.BrownianMotion.ItoIntegral` HTTP 404）。**其余全部为 `[调研代理报告]` 或 `[需进一步核实]`。**
2. **`[实测文档页]` 所服务的源 commit 为 `9e6b3aac99b624d10c84653ab9c5357283b9b3b8`**，**不等于 Mathlib master 当前 HEAD**；且 Mathlib master 的 `lean-toolchain` 为 `v4.35.0-rc4`（报告级）。故「已实测」是**该 commit 时点的实测**。
3. **本文件未运行 `lake build`，未运行 `#print axioms`，未做任何形式化原型。** 因此第二节第三栏的全部「可直接用／需适配」判定，**在通过第六节五道门槛之前，仍是未经准入的线索**。
4. **本文件不虚构文献、链接、声明名、数字。** 凡未查到者写「未查到」；凡未核实的仓库位置写「未定位／未确认」；**不把「未查到」写成「不存在」**。
5. **本文件不给任何年数估计**（依裁决 C 第四节第 2、4 条）。全部规模判断均标注依据来源。
6. **本文件不裁决路线问题。** 与裁决 C 的三处冲突（Q-C1／Q-C2／Q-C3）及 `Causality.Discovery` 的连带决策，**一律标为待作者裁决**，本文件只报告冲突与建议。
7. **本文件的编号对齐**：引用的主文档编号（A10、A15、A19、A20、A23、A32、A33、A34、开放问题 5.4／5.5／6.1／8.1 等）以 `01-理论/10-命运理论-净版.md` 为准；`01-定理清单.md` 的 T 编号（T0.x–T8.x、T9.1–T9.9）与 E 编号（E1–E16）按其自身定义引用；**本文件不新增任何假设编号**。
