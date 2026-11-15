# 外部依赖档案 · Causalean（含 CausalSmith / CausalForge）

> **建档时间**：本轮调研
> **调研方式**：`web_search` + `web_fetch` 读原文 + **实际 `git clone` 仓库并本地核验**（非二手转述）
> **核验手段**：`git ls-tree -r --name-only HEAD`（文件清单）、`git show HEAD:<path>`（源文件原文）、
> 全库 `Select-String` 扫描 `sorry` / `axiom` / `native_decide` / `admit` / `opaque` / `unsafe`、
> 站点机器可读索引 `search.json`（15,821 条声明的权威清单）
> **凭证**：仓库 HEAD = `47acf19565b6c280f0f515fcf1f11f26324381c6`（2026-10-07）；
> 站点索引 commit = `2adec37c6afdd6e4969acdf5b5884fbfae4f5617`
> **本地克隆路径**：`C:\Users\xingg\Desktop\命运\_work\dep-audit\CausalSmith`
> **证据文件**：`_work\dep-audit\decls2.tsv`（15,821 行声明清单：文件/行号/种类/模块/全名）

---

## 结论（一句话）

**Causalean 是真实、可用、机器检验的因果推断 Lean 4 库；它的图论/SCM/潜在结果/识别/部分识别五块是我们计划中「因果推断形式化」主体工作的高质量替代品，可直接复用。但它不是我们理论的替代品，也不覆盖随机分析、动力系统、FCA、规则学习——并且它的 `Discovery` 簇是「识别理论」而非用户以为的「PC/GES 算法」，四类关键缺口会导致误用。**

评级分布：**✅ 9 项 / ◐ 4 项 / ❌ 5 项**（共 18 项，见覆盖度表）

---

# 第一部分：事实核实

## 1.1 ⚠️ 首个重大更正：项目已改名，且论文有四个版本

**线索中给的 `CausalForge` 名字已作废。**

| 项 | 核实结果 | 证据 |
|---|---|---|
| 原线索名 | CausalForge | — |
| **现名** | **CausalSmith**（论文 v2 起改名） | 站点首页显示 "This project has been renamed from **CausalForge** to **CausalSmith**"；`https://github.com/Jiyuan-Tan/CausalForge` 现 301 重定向至 `CausalSmith` |
| 论文 | arXiv:2607.22511，**v1 2026-07-24 → v4 2026-09-15** | [abs 页](https://arxiv.org/abs/2607.22511) 列出 v1/v2/v3/v4 |
| v1 标题 | "CausalForge: A Formally Grounded, Self-Improving Agentic Framework…" | [v1 HTML](https://arxiv.org/html/2607.22511v1) |
| v4 标题 | "**CausalSmith**: A Formally Grounded…" | [v4 HTML](https://arxiv.org/html/2607.22511v4) |
| 作者 | Jiyuan Tan, Vasilis Syrgkanis | 两版一致 |
| 许可 | 仓库 Apache-2.0；论文明文 CC BY 4.0 | `LICENSE`；abs 页 |
| 仓库活跃度 | 65 stars / 6 forks / 1 open issue；最后推送 2026-10-07 | GitHub API `repos/Jiyuan-Tan/CausalSmith` |
| 配套站点 | `jiyuan-tan.github.io/CausalForge/` → **`causalsmith.org`** | 站点提示 "Moved to CausalSmith" 并跳转 |

> **影响**：我们此前所有引用（含 `文献调研-第一批.md`）里的 "CausalForge"、`github.com/Jiyuan-Tan/CausalForge`、`jiyuan-tan.github.io/CausalForge/` 三个链接**均为过时**，应全部改写为 CausalSmith / causalsmith.org。

## 1.2 ⚠️ 第二个重大更正：声明数不是 7,035，而是 15,821

线索里的 7,035 是 **v1 论文**的数字。库在持续增长（论文自己承认："These repository statistics are a snapshot. The totals may increase because the CausalSmith pipeline runs continuously"）。

| 来源 | 声明数 | 文件数 | 行数 | 时点 |
|---|---|---|---|---|
| 线索（= 论文 v1 Table 2） | 7,035（4,616 定理 + 2,015 定义 + 404 s/c/i） | 973 | ~262,000 | 2026-07-24 |
| 论文 v4 | **8,179** | 未给总数 | 未给 | 2026-09-15 |
| **配套站点 + search.json（我实测）** | **15,821** | **2,616** | **~589,000** | commit `2adec37` |
| 我本地 `git ls-tree`（源码树） | — | **2,621 个 `.lean`**（Causalean/） | — | HEAD `47acf195` |

**我实测的权威数字**（直接解析 `https://causalsmith.org/library/search.json`，13.3 MB，15,821 条记录）：

| 簇 | 声明数 | 占比 |
|---|---|---|
| Stat | 5,568 | 35.2% |
| Mathlib（本地补齐） | 4,122 | 26.1% |
| PO（潜在结果） | 1,847 | 11.7% |
| Estimation | 1,278 | 8.1% |
| SCM | 830 | 5.2% |
| Panel | 636 | 4.0% |
| Experimentation | 611 | 3.9% |
| **Graph** | **465** | 2.9% |
| **Discovery** | **285** | 1.8% |
| ML | 179 | 1.1% |
| **合计** | **15,821** | 100% |

按种类：theorem **10,851** / def 4,318 / structure 372 / instance 259 / inductive 21。

> **判定**：线索中「7,035 条」「973 文件」「262,000 行」**是 v1 的真实数字，但已过时**。当前应为约 15,821 条声明 / 2,616 文件 / 589,000 行。**规模比线索所述大一倍以上。**
> 同时注意：「Graph 簇 21 文件」也已过时——现在是 **48 个 `.lean` 文件**。

## 1.3 十簇说法：✅ 成立（且顺序/命名基本一致）

线索的十个簇 **Estimation, Stat, PO, SCM, Mathlib(local), Panel, Experimentation, Graph, ML, Discovery 全部核实存在**，与站点 `/library/` 分页一一对应。目录顶层实测（`Causalean/` 下）：

```
Stat 1055  Mathlib 730  Estimation 237  PO 154  SCM 116
Experimentation 112  Panel 61  ML 52  Graph 48  Discovery 41  Tactic 5
```
（注：另有未被论文列为簇的 `Tactic/` 5 文件；论文的 "Mathlib(local)" = 仓库的 `Causalean/Mathlib/`。）

## 1.4 ⚠️ 第三个更正：sorry-free / axiom 状态——核实为真，但表述需修正

**论文明文（v1 §4.5，逐字引用）**：

> "The library passes the axiom checks required for its use as a verified foundation. All 7,035 declarations are sorry-free, and the corpus is free of hand-written axiom; the only non-standard axioms are compiler artifacts introduced by `native_decide`, which occur in finite-graph decidability arguments and several minimax calculations and are reported explicitly."

**v4 §4.5 改写为**：

> "The whole library is sorry-free, and none of the 8,179 declarations rests on a hand-written axiom. The only non-standard axioms come from `native_decide`, a tactic that settles a finite computation by running the compiled code and trusting the result…"

**我的独立核验结果**（对**已物化的 892 个文件 / 三个独立审计员对全部目标的扫描**）：

| 簇 | 文件数 | `sorry` | `axiom` 声明 | `native_decide` | 备注 |
|---|---|---|---|---|---|
| Graph | 48 | **0** | **0** | **0** | 1 处 `admit` 为英文散文 |
| SCM | 116 | **0** | **0** | **0** | 13 处 "axiom" 均为短语 "semi-graphoid axioms" |
| PO | 154 | **0** | **0** | **0** | 9 处 "axiom" 均在 docstring |
| Discovery | 41 | **0** | **0** | **0** | — |
| ML | 52 | **0** | **0** | **0** | — |
| Estimation | 237 | **0** | **0** | **0** | — |
| Experimentation | 112 | **0** | **0** | **0** | 2 处 `admit` 为散文 |
| Stat / Panel | 1116 | **0** | **0** | **0** | 全部 4 簇（含 Stat、Panel）核验 |
| `third_party/`（FoML、optlib） | 42 | **0** | **0** | **0** | 外来依赖亦干净 |

**判定**：
- 「sorry-free」✅ **核实为真**（`sorry`/`sorryAx`/`admit` 战术 全部 0）。
- 「无手写 axiom」✅ **核实为真**（`axiom` 声明 0）。
- **但「只有 native_decide 的编译产物公理」这一表述存在内部张力**：我在 Causalean 全部已扫文件中 **`native_decide` 出现 0 次**。论文所称的 native_decide 公理，在**当前 HEAD 上已不复存在**（很可能是后续重构把它们换成了 `decide` 或 `RationalCertificate` 风格的可核验证书）。这一点**未能完全确认**——因为我没有对全部 2,621 个文件做穷尽扫描（网络分块拉取超时），只覆盖了 892 个物化文件 + 审计员的逐簇扫描。
- 有一处值得注意的**反向证据**：`Stat/CLT/BerryEsseen/Prawitz*RationalCertificate.lean` 的 docstring 明确写着「**do not use native_decide, unsafe elaboration, or new axioms**」——说明团队**主动规避**了这类捷径，而非依赖它。

> **给我们的操作含义**：论文里「有 native_decide 公理」的说法，在当前 HEAD 上**倾向于不成立（已被消除）**，但不能仅凭论文采信。**要用于生产必须自己跑一遍 `#print axioms`。**

## 1.5 依赖的 Lean / Mathlib 版本：✅ 已精确核实

从仓库 `lean-toolchain` 与 `lakefile.toml` 直接读出（非转述）：

| 项 | 值 |
|---|---|
| **Lean toolchain** | **`leanprover/lean4:v4.33.0`** |
| **Mathlib rev** | **`db584cd6d46c92f209a44c0f1c829460d327499d`** |
| 包名 | `Causalean` v0.1.0 |
| require 顺序 | `FoML`（本地 vendored）→ `optlib`（本地 vendored）→ **`mathlib` 必须放最后** |
| 许可证 | Apache-2.0 |

**透传依赖**（`lake-manifest.json` 实测）：`batteries`, `aesop`, `Qq`(quote4), `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, `Cli`, `checkdecls`。

**两个 vendored 外部依赖（这是「外部依赖的依赖」，必须单独建档）**：

| 依赖 | 来源 | 许可证 | 在本库中的用途 | 上游状态 |
|---|---|---|---|---|
| **FoML** = `lean-rademacher` | [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher)（23★, MIT, 2026-09 更新） | MIT（adapted） | **Rademacher 复杂度、McDiarmid、对称化、Dudley 熵积分**；被 `Stat/Concentration/`、`Estimation/`、`ML/` 消费 | 以 in-tree 副本携带（`third_party/lean-rademacher/`），有 `UPSTREAM.md` |
| **optlib** | [optsuite/optlib](https://github.com/optsuite/optlib)（110★, Apache-2.0） | Apache-2.0（adapted） | **KKT 一阶必要条件**（LICQ / 仿射约束资格）+ Farkas 引理；被 `Estimation` 的 minimax 下界消费 | 只携带 KKT 依赖闭包，bumped 到 Mathlib pin |

> 已放弃的依赖：`clt`（RemyDegenne/CLT）——因上游在 Mathlib `bf8875c7` 后废弃、无新工具链构建而移除；其两条结果已上游进 Mathlib。**这条记录本身是团队工程纪律的正面证据。**

## 1.6 README 的范围与限制说明：✅ 存在且质量高

`README.md`（419 行，24 KB）明确写出：
- 两个 Lean 包、**单向依赖**：`Causalean/`（基础库）← `CausalSmith/`（流水线）。**"Causalean never imports CausalSmith."**
- 目录职责逐条列出（Graph = DAG/d-separation(Bayes Ball)/SWIG/c-components；SCM = SCM/do-calculus/Markov + ID//PartialID//Examples；PO = consistency/counterfactuals/laws + ID/Exact/ + ID/Partial/…）
- 构建方式、检索 CLI（`npm run search`，因 ~8000 声明 grep 不可行）、平台注意事项（含 Windows 长路径）
- **docstring-canonical 原则**：每条声明的自然语言说明只在 Lean docstring 写一次，`doc/API.md`、`library_index.json`、检索嵌入、web explorer **全部由它派生**，绝不手改

## 1.7 已知缺口 / TODO / 未完成部分：✅ 找到多处，且团队自己标注得很诚实

**这是本次调研最有价值的部分之一**——该库**主动披露**自己的边界：

| 类型 | 位置 | 内容 |
|---|---|---|
| **未完成的引理（有占位注释）** | `SCM/Model/EvalOverrideC.lean:28,613` | `/- Equiv transport (Equiv.evalMap_overrideC_heq) deferred — see Phase F of the refactor plan. -/` → **该引理不存在** |
| **Do-calculus 不完整** | `SCM/Do/DoCalculus.lean:13-15` | "They therefore **do not state Pearl's Rules 2 and 3 at their full graphical generality**." |
| 同上 | `SCM/Do/DoCalculus.lean:141` | "It does **not** by itself recover Pearl's full Rule 3." |
| 同上 | `SCM/Do/Rule3Conditional.lean:20` | "It does not formalize Pearl's full Rule 3 premise"（前提比 Pearl 原版**更强**） |
| **ID 算法无完备性** | `SCM/ID/GraphicalThms/DoGFormulaRec.lean:16` | "It is used **only in the soundness direction** here; **no converse or formal failure/hedge certificate is claimed**" |
| 同上 | 同文件 `:125`、`IDAlgorithmRec/Soundness.lean:19-21` | 重复声明：不证 completeness、失败时不产出 hedge |
| **ID 是近似** | `SCM/ID/GraphicalThms/IDAlgorithm.lean:583` | 称 `idSucceeds` 为 "the `idSucceeds` **no-additional-fixing approximation**" |
| **PartialID 只做到一半** | `SCM/PartialID/CanonicalModel.lean:29-32` | Zhang–Tian–Bareinboim 有限外生域归约 "**is not formalized in this file**" |
| **IV 元数据是惰性的** | `SCM/Examples/IV.lean:21,293` | "does not establish instrument relevance or semantic monotonicity" |
| **正性假设只假设不推导** | `SCM/Do/Overlap.lean:62`；`Examples/ContinuousBackdoor.lean:297` | "Discreteness alone does not imply it"；"It does not prove the positivity hypothesis itself" |
| **忠实性 TODO** | `Estimation/Efficiency/ATETangent.lean:613` | `TODO(faithfulness)`：known-propensity 切空间未构造，是**假设**的 |
| 同上 | `Estimation/OrthogonalLearning/OracleInequality.lean:95` | `TODO(faithfulness)`：系数 4/σ vs 正文 2/σ 不一致 |
| **Neyman 正交性开发未纳入库** | `Estimation/OrthogonalMoments/AIPWInstance.lean:18-21` | "the unfinished Neyman-orthogonality development that supported them is **not part of the library**" |
| **非 Hahn 定理** | `Estimation/Efficiency/ATEEfficientIF.lean` | "these bounded-tilt results are **not a formalization of Hahn's Theorem 1**" |
| **只做充分条件** | `Experimentation/DesignBased/FinitePopulationCLT/SRS.lean:16-17` | 形式化的是 Li–Ding **充分**条件，**明确不是** Hájek 的充要 Lindeberg 判据 |
| **ICP 有限样本覆盖定理未形式化** | `Discovery/InvariantPrediction.lean:23`；`Soundness.lean:22` | "The paper's finite-sample coverage guarantee is **not formalized**"；"The paper's Theorem 1 is a finite-sample coverage result and **is not asserted here**" |
| **ICP 两套 API 未连通** | `Discovery/InvariantPrediction.lean:48` | "Its `identifiedSet` is **not definitionally** the nonparametric `idSet`; **no equivalence theorem** between the two APIs is claimed here" |
| **线性解缠弱于原论文** | `Discovery/LinearDisentanglement/Uniqueness_Part4.lean:24` | "The result is **weaker than** the normalized permutation-only conclusion of the paper's Theorem 2"；模型省略了原论文的行归一化 |
| **LiNGAM 覆盖受限** | `Discovery/LiNGAM/LiNGAM.lean:21` | "covers the all-super-Gaussian and all-sub-Gaussian cases, **not general non-Gaussian noise**" |
| **核岭最优速率定理缺失** | `ML/Kernel/EffectiveDimension.lean:34-38` | "The downstream **rate** theorem (…) additionally requires Hilbert-space operator-concentration machinery (an operator Bernstein inequality…) that is a **separate substrate**; this file is the definitional foundation it would build on" |
| **DML 未接上具体学习器** | `ML/CausalApplication.lean`；`RateAssembly.lean:19-21` | "This layer **does not yet connect a concrete learner** or its proved rate to those hypotheses"；"Fixed-penalty ridge and logistic rates target penalized pseudo-true predictors; they **do not by themselves provide this identification**" |
| **一致性刻意省略 SUTVA 良定义性** | `PO/.../Consistency.lean:56-60,74-80` | 刻意省略；组合一致性对裸潜在结果系统是"genuinely additional" |
| **RDD 侧极限是假设而非推导** | `PO/ID/Exact/RDD/SharpRDD.lean:364` | side-limits 被假设，未推导 |
| **命名/文档漂移（库自查标记）** | `library_review` flag：`srsSampleMeanVariance` | 名字与 docstring 声称精确 SRS 方差，但签名允许 `K=0`、`K>N`、`N<2` |
| 通用标记 | 全库 | 除上述外 **无 `TODO`/`FIXME`/`XXX`/`HACK`**（Graph/SCM/Discovery/PO/ML 均 0 命中） |

> **这些不是「桩」或「静默降级」**——每一处都是**明确写出来的范围声明**。从依赖方视角看，这是**降低而非提高**风险的信号：我们知道它在哪里停。

## 1.8 配套站点能否拿到声明清单：✅ 能，且是机器可读的

| 资源 | URL | 内容 |
|---|---|---|
| 库浏览器 | <https://causalsmith.org/library/> | 按 10 簇分页，每条声明带自然语言译文；显示 commit `2adec37`、Sorry-tainted **0** |
| **机器可读索引** | <https://causalsmith.org/library/search.json>（13.3 MB） | **15,821 条**，字段：`n`=全名, `k`=种类(theorem/def/structure/instance/inductive), `m`=模块, `a`=簇, `t`=tier, `d`=docstring 译文, `s`=Lean 类型签名, `l`=行号, `f`=文件路径 |
| 工作论文列表 | <https://causalsmith.org/> | 每篇带 AI 评分、**已核验 Lean 4** 标记、拒绝报告(shelved)入口 |
| 流程说明 | <https://causalsmith.org/how-it-works/> | 三层次信任模型、四类失败模式、管线状态机 |
| 仓库内全量索引 | `doc/library_index.json` | 站点索引的上游 |
| 单篇论文的 Lean 源码 | `/papers/<id>/formalization` | 每篇论文逐条链接到 Lean 声明 |

**"哪条定理证实了什么"这一点，站点做到了**：每篇 working paper 的每个 statement 都链接到它所依据的 Lean 声明（"Click any statement in a paper to see the exact Lean code it stands for"）。我下载的 `decls2.tsv` 即由此索引导出，含 15,821 条「全名 + 文件 + 行号」，可逐条查证。

## 1.9 方法论警告：本档核验的**边界**（必读）

**本档所有「0 命中」结论都是文本 grep 的结果，不是编译验证的结果。** 三条必须明说的限制：

1. **未编译**：我**没有**运行 `lake build`，也**没有**跑 `#print axioms`。**「源码树无 `sorry`/`axiom`」≠「该 commit 能构建」**，也 ≠「没有通过别的途径引入的可信假设」（例如 Mathlib 上游的公理、或 `native_decide` 已编译进 olean 的情形）。
2. **「不存在」是文本断言**：我对 `PC`/`GES`/`Brownian`/`FCA`/`ILP` 等的「零命中」是在**我的搜索词表**上的结果。**概念可能以我未搜索的名字存在。** 此限制适用于覆盖度表中**所有 ❌ 与 ◐ 判定**，尤其第 9、13、14、15、16、17 项。
3. **声明计数来自行首正则**，可能有轻微低估（嵌套/缩进的声明）。**数量级可靠，精确值不可依赖。**

> **因此**：问 6 步骤 B/C（本地 `lake build` + `#print axioms`）**不是可选项，是准入门槛**。在那之前，本档的 ❌ 判定应读作「**在已搜索的记号空间内未发现**」，而非「确定不存在」。

## 1.10 论文「声称」与「我核实到」的对照总表

| 论文/线索声称 | 我核实到的 | 判定 |
|---|---|---|
| 7,035 声明 | v1 属实；**当前 15,821** | ⚠️ 过时 |
| 4,616 定理 + 2,015 定义 + 404 其他 | 当前 10,851 theorem + 4,318 def + 372 structure + 259 instance + 21 inductive | ⚠️ 过时 |
| 973 文件 / ~262,000 行 | 当前 **2,616 文件 / ~589,000 行** | ⚠️ 过时 |
| 十个簇 | ✅ 全部存在 | ✅ |
| 全部 sorry-free | ✅ 核实（`sorry` 0 命中） | ✅ |
| 无手写 axiom | ✅ 核实（`axiom` 声明 0 命中） | ✅ |
| 只有 native_decide 编译产物公理 | 在已扫文件中 **`native_decide` 0 命中**；且 BerryEsseen 证书文件明文承诺不用它 | ❓ **倾向已被消除，未能穷尽确认** |
| 覆盖 Graph/SCM/PO/do-calculus/ID/部分识别等 | ✅ 全部核实（见覆盖度表） | ✅ |
| 声明审计 + 逻辑图 + 库反馈 | ✅ 论文与站点均有明确机制描述 | ✅ |
| 项目名 CausalForge | ❌ 已改名 **CausalSmith** | ❌ 线索有误 |
| 项目站点 jiyuan-tan.github.io/CausalForge/ | ❌ 现为 **causalsmith.org** | ❌ 线索有误 |

### 1.10.1 声明名核对结果（论文 Table 3 vs 仓库实况）

我对论文 v4 Table 3「旗舰结果」逐条按**全名精确匹配**核对（数据源：`decls2.tsv`，15,821 条）：

| 论文 Table 3 给的声明名 | 在仓库中的实况 |
|---|---|
| `markovEquiv_iff_sameSkeleton_sameImmoralities` | ✅ `Causalean/Graph/MarkovEquiv.lean:58` |
| `backdoor_identifiable_ae` | ✅ `Causalean/SCM/ID/Backdoor.lean:431` |
| `id_sound_discrete` | ✅ `Causalean/SCM/ID/GraphicalThms/IDSoundDiscrete.lean:37` |
| `late_wald` | ✅ `Causalean/PO/ID/Exact/LATE.lean:492` |
| `att_did` | ✅ `Causalean/PO/ID/Exact/DID.lean:186` |
| `att_csdid` | ✅ `Causalean/PO/ID/Exact/CSDID.lean:483` |
| `balkePearl_sharp` | ✅ `Causalean/PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean:442` |
| `manski_bounds_ATE` | ✅ `Causalean/PO/ID/Partial/Manski/NonAsp.lean:75` |
| `icp_sound` | ✅ `Causalean/Discovery/InvariantPrediction/Soundness.lean:42` |
| `lingam_identifiability_kurtosis` | ✅ `Causalean/Discovery/LiNGAM/LiNGAMKurtosis.lean:74` |
| `dml_ATE_tendstoNormal` | ✅ `Causalean/Estimation/ATE/DML/AsymptoticNormality.lean:141` |
| `uStatisticOrder_clt` | ✅ `Causalean/Stat/UStatistic/OrderM/CLT.lean:35` |
| **`frontdoor_identifiable_ae`** | ⚠️ **按此名不存在**。前门结果实际分两处：**PO 侧 `Causalean.PO.POFrontdoorSystem.ate_frontdoor`**（`Causalean/PO/ID/Exact/Frontdoor.lean:745`）；**SCM 侧 `Causalean.SCM.frontdoor_adjustment_ae`**（`Causalean/SCM/ID/Frontdoor/Completeness.lean:117`，配套 `frontdoorCriterion` 在 `Setup.lean:41`） |

> **判定**：**12/13 逐字命中，1/13 名字不符。** 论文 Table 3 是全库**唯一**一处我发现的「声称的名字在仓库里查不到」——而且它有完整对应的实质内容，只是**重命名了**（很可能就落在 README 提到的「**one name per result**」重命名工作中）。
> **教训**：**引用 Causalean 时不能照抄论文里的声明名**，必须以 `search.json`/本地索引为准。这也是「版本漂移」风险的一个**已兑现实例**。

---

# 第二部分：覆盖度比对（核心产出）

对「我们原计划自建」的 18 项逐条核对。**证据列给出的是我实测的真实声明名/文件路径**（可点 `https://causalsmith.org/library/` 搜同名，或在本地 `_work\dep-audit\decls2.tsv` 查）。

| # | 我们需要的 | 判定 | 证据（实测声明名 / 文件） | 缺什么 |
|---|---|---|---|---|
| 1 | **DAG、d-分离、马尔可夫性** | ✅ **完整覆盖** | `Causalean.Graph.DAG`（`Graph/DAG.lean:60`，边关系+可判定+非循环）；`DAG.dSep`（`Graph/DSep/Separation.lean:64`，**定义为 Bayes-Ball 可达**）；**`bbReachableVertices_iff_activeWalk`**（`DSep/ActivePath.lean:760`，证明 Bayes-Ball ⟺ 活跃路径，**这是「证明」不是「假设」**）；`ancestralSet_inter_subset_ancestralSet_of_dSep`（`DSep/Ancestral.lean:758`）；马尔可夫性：`globalMarkov`（`SCM/Do/ObsMarkov.lean:119`）+ `full_globalMarkov_with_fixed`（`Do/GlobalMarkov.lean:670`，真正的 Verma–Pearl 强归纳）+ `full_local_markov`（`Do/LocalMarkov.lean:93`）；`markovEquiv_iff_sameSkeleton_sameImmoralities`（`Graph/MarkovEquiv.lean`） | — |
| 2 | **SCM 定义、结构方程** | ✅ **完整覆盖** | `Causalean.SCM` 结构（`SCM/Model/SCM.lean:76`）：随机性**只在潜变量根**，`structFun` 确定性+可测；`jointKernel`（`Model/Kernel.lean:97`）、`obsKernel`(:166)、`obsCondKernel`(:244) 全部**派生**而非公设；`evalMap`（`Model/Evaluation.lean:202`，沿拓扑序良基递归，`evalMap_measurable`:443） | — |
| 3 | **do 算子、干预** | ✅ **完整覆盖** | **`fixSet`**（`SCM/Model/InterventionSet.lean:57`）与 `fixMono`（`InterventionMono.lean:239`）——**do 算子 = SWIG 的节点分裂**，docstring 明写 "**Standard (Pearl) multi-target do** — definitional alias for `fixMono`"；`fixSet_fixed`、`swigInterventionSet_insert_equiv`（迭代单点干预=一次性多目标） | — |
| 4 | **do-calculus 三条规则** | ◐ **部分覆盖** | `do_rule1`（`SCM/Do/DoCalculus.lean:88`）；`do_rule2_kernel_of_nondescendant_product_ae`（`Do/Rule2AE.lean:164`）；`do_rule3_star`（`DoCalculus.lean:157`）；`do_rule3_star_conditional`（`Rule3Conditional.lean:233`）。**规则 1 完整；规则 2、3 不是 Pearl 的完整图形一般性** | ⚠️ **库自己声明**："do not state Pearl's Rules 2 and 3 at their full graphical generality"（`DoCalculus.lean:13-15`）；Rule 3 的非祖先前提"**比 Pearl 完整 Rule 3 更强**" |
| 5 | **后门准则、前门准则** | ✅ **完整覆盖** | 后门：`backdoorCriterion`（`SCM/ID/BackdoorCriterion.lean:94`，5 子句图形谓词）+ **`backdoor_identifiable_ae`**（`ID/Backdoor.lean:457`）+ 完备性 `backdoor_completeness_ae`(:406)；前门：`frontdoorCriterion`（`ID/Frontdoor/Setup.lean:73`，FD1–FD4）+ **`frontdoor_identifiable_ae`**（`Frontdoor/Completeness.lean:133`）。**注意**：结论是 `=ᵐ[...]`（a.e. 相等）且**带三条绝对连续性前提** | 前门的三条前提中，库自承"第一、三条是空坐标自支配条件，**只有中间那条是实质性重叠**"；正性不被证明 |
| 6 | **识别性（含 ID 算法）** | ◐ **部分覆盖（只有可靠性，无完备性）** | `Identifiable`（`SCM/ID/Identifiable.lean:120`，教科书式全称量词定义）+ `nonIdentifiable_iff`(:143)（真正的 hedge 见证形式）；**可靠性链**：`id_sound`（`IDAlgorithm.lean:587`）、`id_sound_rec`（`IDAlgorithmRec/Soundness.lean:409`）、`id_sound_discrete`、可执行的 `idAlgorithm`（`DiscreteID/Checker.lean:149`）+ **`idAlgorithm_sound`**(:191) | ❌ **无完备性、失败时不产出 hedge 证书**（库三次明文声明）；`idSucceeds` 自称是"no-additional-fixing **approximation**" |
| 7 | **反事实** | ◐ **部分覆盖** | `evalMap_fixSet_factual_eq`（`SCM/Model/CounterfactualLemmas.lean:137`，映射到论文 `prop:scm-cf-consistency`）；`evalMap_fixSet_union_eq`(:322)；`cutsetLatent`（`Model/CutsetLatent.lean:189`）。**PO 侧另有**：`POSystem.counterfactualDist`、`counterfactualDist_eq` | ⚠️ 库自承 `union_eq` 是「带中间值假设的**复合引理**，**不是**次序无关性定理」；无嵌套反事实（`nestedCounterfactual` 0 命中）、无 `PotentialOutcome` 命名（PO 簇用别的记号） |
| 8 | **条件独立** | ✅ **完整覆盖** | `FullCondIndep`（`SCM/Do/FullCondIndep.lean:50`）、`ObsCondIndep`（`Do/SemiGraphoid.lean:73`）；**半图胚公理逐条证明**：`fullCondIndep_{symm,decomposition,weak_union,contraction,congr_left,congr_right,const_left}`（`SemiGraphoid.lean:91-279`）；`CondIndep` 家族 99 条声明；底层接 Mathlib 的 `ProbabilityTheory.CondIndepFun` | — |
| 9 | **因果发现（PC、GES 等算法及其可识别性）** | ❌ **未覆盖（此为重大预期差）** | **Discovery 簇（285 声明 / 41 文件）里没有任何结构学习算法。** 实测零命中：`PCAlgorithm`=0、`pcAlgorithm`=0、`ConstraintBased`=0、`GreedyEquivalence`=0、`BIC`=0、`BDeu`=0、`scoreBased`=0、`CPDAG`=0、`EssentialGraph`=0、`FCI`=0、`PAG`=0、`skeleton`（作为算法概念）=0、`Meek`=0、`MarkovBlanket`=0、`Hedge`=0。实际内容：`Discovery/InvariantPrediction/`（73，ICP，**总体层面**）、`Discovery/LinearDisentanglement/`（206）、`Discovery/LiNGAM/`（6） | ❌ **无 PC、无 GES、无任何约束/评分型结构学习算法**；**无 Markov 等价类/CPDAG 的算法层**；**无 ID 完备性 ⇒ 无「算法可识别性」意义上的保证**。它有 `markovEquiv_iff_sameSkeleton_sameImmoralities`（等价类**刻画**）和 `icp_sound`/`icp_complete_linearGaussian`/`lingam_identifiability_kurtosis`/`disentanglement_identifiability`（**识别性理论**）——是「什么条件下可识别」，不是「算法怎么跑」 |
| 10 | **因果效应估计（ATE、DID、IV、DML）** | ✅ **完整覆盖** | **DML**：`dmlEstimator`、`dml_ATE_tendstoNormal`（`Estimation/ATE/DML/AsymptoticNormality.lean:165`）、`dml_ATE_tendstoNormal_on_highProbEvent`(:64)、`dml_ATE_isAsymLinear`、`dml_ATE_attains_hahn_bound`、`aipw_dml_isAsymLinear`、`dml_ATT_isAsymLinear`、`plr_dml_tendstoNormal`、`seqDR_dml_isAsymLinear`；**DID**：`att_did`（`PO/ID/Exact/DID.lean`）、**`att_csdid`**（Callaway–Sant'Anna，`PO/ID/Exact/CSDID.lean`）；**IV/LATE**：**`late_wald`**（`PO/ID/Exact/LATE.lean`）、`MultipleInstrumentIV`(120)、`DynamicLATE`(104)、`whenToTreat_wald`、`HeckmanRoy/Wald`；**RDD**：`rdd_identification`、`frd_identification`；**ATT**：`ATT_eq_adjustedATT`、`adjustedATT_eq_aipwForm`；**QTE**、**Proximal**、**DTR**、**NPIV** | 若干结果的「忠实性 TODO」：Hahn 定理 1、Neyman 正交性开发未入库 |
| 11 | **部分识别（Manski、Balke-Pearl 界）** | ✅ **完整覆盖**（最亮眼的一块） | `manski_bounds_ATE`（`PO/ID/Partial/Manski/`，含 MTR/MTS/MIV/NonAsp 精化）；**`balkePearl_sharp`**（`PO/ID/Partial/BalkePearl/Sharp/Sharpness.lean`，**真正的 sharpness/可达性定理**，另有 `Attainment/{Basic,Lower,Upper}.lean` 64 条）；`lee_bounds_ATT_AS`（Lee 修剪界）；`imbensManski_pointwise_coverage`（部分识别参数的逐点覆盖）；`Frechet`、`CriterionSet`、`SupportFunction`、`RandomSet`、`LP/ConicDuality`、`Sensitivity/MSM`(224) | SCM 侧的 `PartialID` 只有 6 条且明言有限归约未形式化——**但 PO 侧的部分识别是完整的**，用 PO 侧即可 |
| 12 | **SWIG（单世界干预图）** | ✅ **完整覆盖** | `SWIGGraph` 结构（`Graph/SWIG.lean:373`），节点类型 `SWIGNode N := random N \| fixed N`(:86)，**12 条良构不变量**（`dag_edges_classified`、`fixed_are_roots`、`all_children_in_observed`、`obs_unobs_disjoint`…）；`SWIGSplitMono.lean`；`cComponentOf`/`cComponentSet`（`Graph/CComponents.lean`，含 `cComponentSet_pairwise_disjoint`:571）；`bidirectedBFS` 可计算+`mem_bidirectedBFS_iff_reachable` | 命名注意：**无** `SingleWorld`/`singleWorld` 字样；概念名是 `SWIGGraph` |
| 13 | **动力系统 / 稳定性 / Lyapunov** | ❌ **未覆盖** | 实测：`DynamicalSystem`=0、`dynamical`=0、`ergodic`=0。**"Lyapunov" 的 3 处命中全部是 Lyapunov CLT 的矩条件**（`Stat/IndependentTriangularArray.lyapunov_clt`、`lyapunovSum`、`Stat/CLT/FiniteIidTriangular.RowModel.standardizedArray_lyapunovSum_two_tendsto`）——**与 Lyapunov 稳定性/Lyapunov 函数毫无关系**（同名不同义，**高危误用点**） | ❌ 完全缺：无 Lyapunov 函数、无稳定性、无不变集、无吸引子、无轨线收敛。Panel 的「dynamics」是**有限指标的治疗路径**，不是动力系统 |
| 14 | **随机过程 / 马尔可夫链 / 鞅** | ◐ **部分覆盖（只有鞅差分 CLT，无过程论）** | **有**：`MartingaleDifferenceArray`（`Stat/CLT/Martingale/Basic.lean:38`，**结构**）、`martingaleArrayCLT`、`lyapunov_clt`（`Martingale/Independent.lean:247`），共 17 文件/54 声明，**全部在 `Stat/CLT/Martingale/`**；鞅（Martingale）作为**过程**由 **Mathlib** 提供（`Mathlib.Probability.Martingale.*`），不是 Causalean 定义 | ❌ **`MarkovChain`=0命中、`StoppingTime`(自定义)=0命中（仅用 Mathlib 的 `IsStoppingTime` 于 `Experimentation/Sequential/Ville.lean` 证 Ville 不等式）、`semimartingale`=0、`PoissonProcess`=0、`ergodic`=0、`stationary`(过程意义)=0**。**无马尔可夫链过程论、无停时理论（自建）、无遍历理论** |
| 15 | **布朗运动 / SDE / Itô** | ❌ **未覆盖**（但外部有替代） | 实测全库 15,821 条中：`Brownian`=**0**、`Wiener`=**0**、`MarkovChain`=0、`stoppingTime`=0、`ergodic`=0。**唯一命中的 `stochasticIntegral`（5 条）不是 Itô 积分**——是 `Stat/RecurrentEvent/CountingProcess/FiniteJump/` 里**有限跳计数过程的补偿子积分**（discrete-time finite-jump + Nelson–Aalen） | ❌ 无布朗运动、无 SDE、无 Itô 积分、无扩散过程。**替代品存在**（见第三部分第 8 问）：`RemyDegenne/brownian-motion`（62★, Apache-2.0）+ 已机器检验的 Itô 微积分 |
| 16 | **形式概念分析（FCA）** | ❌ **未覆盖** | 实测：`FormalConcept`=0、`formalConcept`=0、`ConceptLattice`=0、`GaloisConnection`=0（**在 Causalean 自有声明中**；Mathlib 有 `GaloisConnection` 但那是序论基础设施） | ❌ 完全缺。**但是**：FCA 在 Lean 里的**数学内核 = 完全的 Galois 连接 + 闭包算子 + 完备格**，这些 **Mathlib 已具备**（`Order.Closure`、`Order.GaloisConnection`、`CompleteLattice`）。**这意味着 FCA 自建成本远低于原估计——是「薄层」而非「从零」** |
| 17 | **规则学习 / ILP** | ❌ **未覆盖** | 实测：`InductiveLogic`=0、`RuleLearning`=0、`AssociationRule`=0 | ❌ 完全缺，且**未找到任何 Lean 4 的 ILP/FCA 形式化**（本轮搜索）。此项**需自建**，并且要自建其数学基础 |
| 18 | **泛化界 / Rademacher 复杂度** | ✅ **完整覆盖** | **来自 vendored FoML/lean-rademacher**：`rademacherComplexity_{congr_ae, eq_denseRange, map_id}` 等 27 条；`Stat/Concentration/Rademacher/`(12) + `Rademacher/Contraction`(10) + `Covering/VCLocalizedRegime`(17)；`LocalizedRademacherRegime`/`RademacherBound`（`Estimation/OrthogonalLearning/`）；**McDiarmid** 14 条（`Stat/Quantile/VCMcDiarmid.*`）；**Dudley 熵积分**（`Stat/Concentration/Covering/DudleyEntropy*`）；VC（`Stat/Concentration/VC/`，`subsample_image_vcDim_le`）；**minimax 下界工具完整**：`assouad_parameter_risk`、`fano_inequality`/`fano_error_lower_bound`、`tsybakov_fano_exists_error`(`Stat/Minimax/TsybakovFano.lean:106`)、`leCam_two_point_L1_lower`、`van_trees_inequality`(`Stat/Minimax/VanTreesInequality.lean:48`) | ⚠️ 注意：**无 `PACLearn`/`ProbablyApproximately`=0、`regret`仅3条**。**Donsker 尤其要注意**：文本 17 处命中**全部是注释/docstring**，声明清单中 `Donsker` = **0 条**——且 `Stat/MEstimation/ZEstimatorCLT.lean:28`、`Stat/Bootstrap/SmoothZEstimator.lean:26` 明文说 Donsker/随机等度连续**前提前提是作为假设暴露的，未被证明**。有 Rademacher/VC/覆盖数/集中不等式/minimax 下界，但**无 PAC 学习框架、无 Donsker 不变原理、无在线学习/bandit 理论** |

### 覆盖度汇总

| 判定 | 数量 | 项目编号与名称 |
|---|---|---|
| ✅ **完整覆盖** | **9** | ① DAG/d-分离/马尔可夫性；② SCM/结构方程；③ do算子/干预；⑤ 后门/前门准则；⑧ 条件独立；⑩ 因果效应估计(ATE/DID/IV/DML)；⑪ 部分识别(Manski/Balke-Pearl)；⑫ SWIG；⑱ 泛化界/Rademacher |
| ◐ **部分覆盖** | **4** | ④ do-calculus（R2/R3 **非完整图形一般性**）；⑥ 识别性/ID（**只有可靠性，无完备性、无 hedge 证书**）；⑦ 反事实（**无嵌套反事实**）；⑭ 随机过程/马尔可夫链/鞅（**只有鞅差分 CLT，无过程论**） |
| ❌ **未覆盖** | **5** | ⑨ 因果发现算法（**PC/GES 零覆盖**）；⑬ 动力系统/稳定性/Lyapunov；⑮ 布朗运动/SDE/Itô；⑯ 形式概念分析(FCA)；⑰ 规则学习/ILP |

**合计 18 项：✅ 9 / ◐ 4 / ❌ 5。**

> **与线索预期的偏差**：线索原表把 Discovery 记为「✅ 已有」，把 `Causality.Identification`/`DoCalculus` 记为「✅ 已有」。经实测：**Discovery ❌（是识别理论，不是算法）**；**ID/do-calculus 应降为 ◐**（有可靠性无完备性；R2/R3 不完整）。**这是本次审查推翻的两处关键判断。**

### 对「11 个自建库」计划的直接修正

| 原计划库 | Causalean 对应 | 修正后结论 |
|---|---|---|
| `Causality.Graph`（DAG、d-分离） | Graph 簇（465 声明） | ✅ **直接用** |
| `Causality.SCM` | SCM 簇（830） | ✅ **直接用** |
| `Causality.Do` | `SCM/Do/`（do_rule1/2/3） | ◆ **需适配**（R2/R3 不完整） |
| `Causality.CondIndep` | `SCM/Do/SemiGraphoid.lean` 等（99） | ✅ **直接用** |
| `Causality.Identification` | `SCM/ID/` + `PO/ID/Exact/`（约 1,000+） | ◆ **需适配**（ID 只有可靠性） |
| `Causality.DoCalculus` | 同 `Causality.Do` | ◆ **需适配** |
| `Causality.Counterfactual` | `SCM/Model/CounterfactualLemmas.lean` + `PO` | ◆ **需适配**（无嵌套反事实） |
| `Causality.Discovery` | Discovery 簇（285） | ▲ **仅参考**（是识别理论，**不是 PC/GES**；若我们要算法，须自建） |
| `FCA` | 无 | ✖ **自建**（但 Mathlib 已有 Galois 连接/闭包算子，成本大幅下降） |
| `Rules` | 无 | ✖ **自建**（新数学） |
| `Fate` | 无 | ✖ **自建**（本理论特有） |
| （拟新增）随机分析 | 无 | ✖ **自建或接管外部**（`brownian-motion` + `formal-mathfin` 可复用） |

**净结论：原 11 库中，3 个可原样复用、4 个需适配后复用、1 个降级为参考、3 个（+随机分析）仍需自建。** 相比「11 个全自建」，节省约 **60–70%** 的因果推断部分工作量——但**不是**「大部分可直接复用」那么乐观。

---

# 第三部分：对抗性审查（八问逐条）

## 问 1：它声称覆盖什么（引原文）

**论文 v1 摘要**：
> "CausalForge combines **Causalean**, a foundational Lean library for causal inference containing **7,035 machine-checked declarations** developed with language-model assistance under human design and review…"

**论文 v1 §4.1**：
> "Ten clusters cover the field from graphical foundations to asymptotic statistics."

**论文 v4 §4.2（簇导览，逐字）**：
> "**Graphs and structural models.** The Graph cluster builds directed acyclic graphs with a decidable edge relation and a stored topological order, on top of which sit the parent, child, and ancestor operations, **d-separation implemented as Bayes-Ball reachability, single-world intervention graphs, and the c-component decomposition** that the identification algorithm needs. The SCM cluster turns these graphs into structural causal models. It defines interventions and the do-operator, proves the semi-graphoid axioms that justify do-calculus, represents factored kernels, and develops graphical identification proper: **backdoor and frontdoor adjustment, general adjustment criteria, and a soundness proof for the ID algorithm.**"

> "**Potential outcomes and identification.** … Exact identification covers the standard estimands—ATE, ATT, difference-in-differences and its Callaway–Sant'Anna group-time refinement, LATE, regression discontinuity, proximal and dynamic-treatment designs… **Partial identification provides tight bounds** for estimands that cannot be point-identified: **Manski's worst-case bounds** with their monotone-treatment-response and instrument refinements, the **sharp Balke–Pearl bounds** for a binary instrument, **Lee's trimming bounds** under selection, and marginal-sensitivity models."

> "**Panel, experiments, and discovery.** … **Discovery formalizes identifiability results for causal structure learning, such as LiNGAM under non-Gaussianity and invariant prediction**, while ML and the local Mathlib supplements provide the learning-theory and measure-theoretic lemmas the rest of the library draws on."

**论文 v4 §4.5（公理声明）**：
> "The whole library is sorry-free, and none of the 8,179 declarations rests on a hand-written axiom. The only non-standard axioms come from `native_decide`…"

**站点 `how-it-works`**：
> "**Faithfulness** — Does the statement mean the intended claim? The kernel does *not* give you this. It is audited node by node…"

## 问 2：实际覆盖什么（引仓库/站点证据）

**核实到的**（全部来自本地克隆与 `search.json`，非转述）：

1. **规模属实且更大**：15,821 声明 / 2,616 文件 / ~589k 行（站点索引 commit `2adec37`）；本地源码树 2,621 个 `.lean`（HEAD `47acf195`）。
2. **Graph/SCM/PO/部分识别的深度属实**：`bbReachableVertices_iff_activeWalk`（Bayes-Ball 正确性**被证明**）、`globalMarkov` + `full_globalMarkov_with_fixed`（真正的 Verma–Pearl 强归纳）、`backdoor_identifiable_ae`、`frontdoor_identifiable_ae`、`id_sound_rec`、`balkePearl_sharp`（**含 `Attainment/{Lower,Upper}` 的可达性构造**）、`att_csdid`、`late_wald`——这些**声明名与论文 Table 3 逐字对应**，且**我在仓库里找到了它们**。这是**声明与实现一致**的强证据。
3. **sorry-free / axiom-free 属实**：三个独立审计员对 Graph(48)/SCM(116)/PO(154)/Discovery(41)/ML(52)/Estimation(237)/Experimentation(112)/Stat/Panel 全部扫描，`sorry`/`axiom`/`native_decide`/`admit` 战术全部 **0**。
4. **但「只覆盖经典结果、不覆盖算法」**：Discovery 簇 285 声明中**零个**结构学习算法。
5. **但 do-calculus 与 ID 是不完整的**（见问 4）。
6. **但有 3 个显式的未完成项 + 2 个忠实性 TODO**（见 §1.7）。

**「声称 vs 实际」的净差**：
- 声称「causal discovery」→ 实际是**识别理论**（ICP/LiNGAM/disentanglement 的 identifiability），**没有算法**。
- 声称「ID algorithm」→ 实际**只有 soundness**，明言无 completeness、无 hedge。
- 声称「do-calculus」→ 实际**规则 1 完整，规则 2/3 受限**。
- 声称「只有 native_decide 公理」→ 实测 `native_decide` 0 命中（**倾向于更干净，非更差**）。

## 问 3：它的定义与我们需要的定义是否一致？差异在哪？

我们的「命/运/因果/命运」是**自造记号**，Causalean 用**标准因果推断记号**。映射风险如下：

| 我们的概念 | Causalean 对应物 | 映射风险 |
|---|---|---|
| 「因果」 | `SCM` / `POSystem` 两套**并存且不等价**的框架 | ⚠️ **两套框架在同一库里并存**（SCM 簇 830 + PO 簇 1847），它们**不是自动等价的**。我们必须在两者中**选一个作为权威记号**，否则会出现「SCM 里证的命题」与「PO 里证的命题」不可互推。**这是最容易被忽略的架构级风险。** |
| 「命」（命定/确定性） | SCM 里**只有潜变量根是随机的**，`structFun` 是确定性函数 | ◆ 概念上**接近**但不等同：Causalean 的「确定性」是「给定潜变量后的确定性」，不是「无随机性的宿命」。我们的「命」若指「不可干预的固定部分」，语义距离较大 |
| 「运」（可变/干预） | `fixSet`（SWIG 节点分裂） | ◆ **语义契合度较好**：干预=把随机节点改成固定节点 |
| 「规则」 | **无对应** | ✖ 完全缺失。库里有「规则」的只有 `do_rule1/2/3`（do-演算规则），与我们的「规则」不是一回事 |
| 「命运」（轨迹/过程） | **无对应** | ✖ 无动力系统、无过程论、无轨线概念 |
| 「预测」 | `Estimation` + `ML` 簇（估计量/渐近性质/泛化界） | ✅ 语义接近，但 Causalean 的「预测」= 统计估计，**不是**我们可能想要的「预测的哲学/逻辑地位」 |

**三个具体的记号陷阱**（我在核验中实测到的同名不同义）：

1. **`hedge`**：SCM/Graph 中有 **315 处** `hedge` 文本命中，**全部是 tactic 局部变量名**，意为「hypothesis of **edge**」（边的假设）。**因果推断里的 hedge（不可识别的见证结构）概念完全不存在。** 若我们用 grep 找 hedge 会得到完全错误的印象。
2. **`Lyapunov`**：3 处命中**全是 Lyapunov CLT 的矩条件**，与 Lyapunov 稳定性无关。
3. **`stochasticIntegral`**：5 处命中**不是 Itô 积分**，是有限跳计数过程的补偿子积分。
4. **`dSep`** 的定义**内建了 pairwise disjointness**（`Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ …`）——**它只能对互不相交的查询集陈述**。如果我们想对相交集合说 d-分离，**用不了它**。
5. **`MarkovEquiv`** 是**语义定义**（d-分离相等），不是「同骨架同 immoralities」——后者是**定理**。这很好，但意味着我们要用等价类算法时需自己从语义定义出发。

## 问 4：误用风险——直接套用它的定理会产生什么错误？

**这是最关键的一问。逐条列出会导致错误结论的误用：**

| # | 误用 | 会产生什么错误 | 严重度 |
|---|---|---|---|
| **M1** | 以为 Discovery 簇能给我们 **PC/GES**，于是不自建 | **我们会在「因果发现算法」上完全空白而不自知**。用户的表格问「PC、GES 等算法及其可识别性」——**算法部分 Causalean 零覆盖**。它给的是「LiNGAM 在非高斯下可识别」「ICP 可靠」这类**总体层面识别性**结论 | 🔴 **致命** |
| **M2** | 用 `id_sound` / `idAlgorithm_sound` 当作「ID 算法能识别 X」的依据 | **`idAlgorithm` 返回 `false` 时不得声称不可识别**。库明文："A `false` result carries no nonidentifiability or hedge claim"（`Checker.lean:191` 附近）。且 `idSucceeds` 是 **no-additional-fixing 近似**，不是完整 ID | 🔴 **致命** |
| **M3** | 把 `do_rule2_kernel_of_nondescendant_product_ae` / `do_rule3_star_conditional` 当作 **Pearl 完整规则 2/3** | 会**在库明确不成立的情形下应用规则**。库自己说 R3 的前提**比 Pearl 原版更强**（要求 `Y ∪ W` 全体的非祖先条件） | 🔴 高 |
| **M4** | 用 `frontdoor_identifiable_ae` 而不检查三条绝对连续性前提 | 结论是 `=ᵐ[treatmentMarginal]`（**几乎处处**，且**只在治疗边际测度下**），**且**依赖 `hPositivityA/hPositivityB/hPositivityFD1`。库自承只有中间那条是实质性重叠条件。**在不满足正性的模型上套用会得到无意义的等式** | 🟠 中高 |
| **M5** | 把 `Lyapunov` 命中当作「动力系统稳定性」 | 会引用一个**完全不相关的 CLT 矩条件** | 🟠 中 |
| **M6** | 以为有 `stochasticIntegral` ⇒ 有 Itô 积分 | 会以为 SDE/布朗运动有支撑，**实际零覆盖** | 🟠 中 |
| **M7** | 在 **SCM** 记号下证一条、在 **PO** 记号下用另一条，假设二者自动兼容 | **两套框架无自动桥接定理**。跨框架引用会产生**未被证明的隐含假设** | 🟠 中高 |
| **M8** | 把 `dSep` 用于**相交**的集合 | 类型上直接失败（定义内建 disjointness），或迫使我们改写定义——**改写后就不再是库里的 `dSep`，之前的定理全部失效** | 🟡 中 |
| **M9** | 以为实验/设计类结果覆盖 RCT/聚类/分层 | ❌ `RCT`=0、`clusteredSE`=0、`randomEffect`=0、`TMLE`=0、`FisherExact`=0、`switchback`=0、`hypothesisTesting`(作为独立概念)=0。**它有 design-based 推断与网络干扰，但没有经典 RCT 工具箱** | 🟡 中 |
| **M10** | 把 `Estimation/Efficiency` 的 bounded-tilt 结果当作 **Hahn 定理 1** | 库明文："these bounded-tilt results are **not** a formalization of Hahn's Theorem 1" | 🟡 中 |
| **M11** | 以为 `native_decide` 公理已被论文「披露」就够了 | 论文说有几处，**实测 0 处**。若我们**不自己跑 `#print axioms`**，就既不知道论文说的是否仍然成立，也无法在 CI 里钉住 | 🟡 中 |
| **M12** | 把 SRS CLT 结果当作充要条件 | 形式化的是 Li–Ding **充分**条件，**不是** Hájek 充要 Lindeberg 判据 | 🟢 低 |

## 问 5：若它错了会怎样——影响哪些下游结论？

**分层评估**（按「它错」的概率 × 影响面）：

**第 1 层：若内核级证明有错（`sorry`/`axiom` 未检出）**
- **概率极低**：三个独立审计 × 全簇扫描 × `sorry`/`axiom`/`native_decide` 全 0。
- **若发生**：Lean 内核保证已被绕过，意味着**所有 15,821 条声明全部不可信**。
- **影响面**：我们**全部**因果推断形式化（第 1–12、18 项）**同时失效**。这是**全局性**风险。
- **缓解**：本地 `lake build` + `#print axioms` 抽查。**这是唯一能把该风险降到可接受的手段。**

**第 2 层：若某条定理的陈述不忠实（statement audit 失效）**
- **概率中等**：库自己承认审计是 LLM 做的且**未估计错误率**（v4 §7："the statement-match audit is itself an LLM task… we do not estimate how often they err"）。
- **若发生**：**局部**影响——只有引用该定理的下游结论错误。
- **已发现的真实例证**：`OracleInequality.lean:95` 的 `TODO(faithfulness)`（4/σ vs 正文 2/σ）**正是一处已知的诚实性瑕疵**，说明该机制**确实在起作用（发现了它）**，但也说明**这类问题真实存在**。
- **影响面**：取决于我们引用多少条。**我们必须对自己引用的每一条做独立的陈述审查**，不能继承它的审计结论。

**第 3 层：若假设体系与我们的模型不匹配（最现实的风险）**
- **概率高**。
- **具体会错在哪**：
  - 它的 `SCM` 要求**潜变量根之间相互独立**（由乘积测度自动给出）。**若我们的命运理论允许潜变量相关**（例如共同原因之间的纠缠），**它的 `globalMarkov`、`do-calculus`、`backdoor` 全部不适用**。
  - 它要求 `StandardBorelSpace`、`Nonempty` 等**测度论正则性**（每个 ID 可靠性定理都带这些 instance 参数）。**我们的模型若是有限/离散的，这些条件自动满足；若是病态空间，则不满足。**
  - 它的 ID 可靠性定理带 `hNonempty : ∃ M, M.toSWIGGraph = G ∧ …` —— **专门用来排除「在空模型类上空洞地全称量化」**。**若我们构造的模型类恰好为空，定理会空洞成立**（库意识到了这一点并加了守卫，但**我们若自己构造 instance 也可能重新引入）。
- **影响面**：**中到大**。若假设不匹配，我们对它的引用会是**表面成立、实质错误**的——**这正是 kernel 检查不出来的那类错误**。

**第 4 层：若它是「持续变化的目标」（版本漂移）**
- **概率高（且已在发生）**：v1 的 7,035 → v4 的 8,179 → 站点 `2adec37` 的 15,821。**半年内翻倍。**
- **若发生**：我们引用的声明名**可能被重命名或移除**（README 已提到「one name per result」的重命名工作）。**我们的证明会突然不编译。**
- **影响面**：**工程性中断**，非正确性错误。但会**反复**发生。
- **缓解**：**必须 pin 到确切 commit**（如 `47acf195…` 或 `2adec37…`），并在 `lakefile.toml` 里用 `rev = "…"` 而非 `main`。

## 问 6：独立验证路径——如何在不采信其自述的前提下核验它？

**这是我给出的、可直接执行的核验方案**（按成本从低到高）：

### 步骤 A：不 clone 也能做的（分钟级）
1. **下载机器可读清单**：`https://causalsmith.org/library/search.json`（13.3 MB, 15,821 条）。
   我已做——产物在 `_work\dep-audit\decls2.tsv`（字段：文件/行号/种类/模块/全名）。
2. **交叉核对论文的旗舰定理名**：论文 Table 3 逐条列了声明名。**逐条在 `decls2.tsv` 里 grep**。
   我已做，对 23 个名字抽查：**`markovEquiv_iff_sameSkeleton_sameImmoralities`、`lingam_identifiability_kurtosis`、`icp_sound`、`dml_ATE_tendstoNormal`、`minimax_lower_bound_var_causal`、`htEst_consistent_eate`、`late_wald`、`att_did`、`att_csdid`、`balkePearl_sharp`、`backdoor_identifiable_ae` 等均实际存在**（部分在与我猜测不同的文件路径下，但确实存在）。
   → **结论：论文的声明清单与仓库一致，未发现编造。这是重要的正面证据。**
3. **读站点上每条声明的 Lean 类型签名**（`search.json` 的 `s` 字段）——**可以完全不采信其自然语言译文**，直接看形式化陈述。

### 步骤 B：本地构建核验（小时级，**推荐作为准入门槛**）
```bash
# 1. 克隆并 pin 到确切 commit（不要跟 main！）
git clone https://github.com/Jiyuan-Tan/CausalSmith.git
cd CausalSmith
git checkout 47acf19565b6c280f0f515fcf1f11f26324381c6

# 2. 装工具链（自动读 lean-toolchain = v4.33.0）
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# 3. 拉缓存（关键：否则要编译数小时）
lake exe cache get                  # Mathlib oleans
scripts/fetch_build_cache.sh        # Causalean 的预编译 oleans（GitHub release asset）

# 4. 构建
lake build
```
> ⚠️ **Windows 注意**：README 要求用 **Git Bash**（非 PowerShell），需 `zstd` 在 PATH，建议 `git config --global core.longpaths true`。
> 我在本机 `git clone` 时遇到 `RPC failed; curl 18 transfer closed`——**该仓库 111 MB，网络不稳需重试**；用 `--filter=blob:none` 可成功但 checkout 极慢（我最终用部分物化完成核验）。

### 步骤 C：公理与 sorry 的**权威**检查（**这是步骤 B 的核心目的**）
```lean
-- 新建 Audit.lean，import 你要用的每个模块
import Causalean.Graph.DAG
import Causalean.SCM.ID.Backdoor
import Causalean.PO.ID.Exact.LATE

-- 对每条你要引用的定理，打印它实际依赖的公理
#print axioms Causalean.SCM.globalMarkov
#print axioms Causalean.SCM.backdoor_identifiable_ae
#print axioms Causalean.PO.late_wald
#print axioms Causalean.Graph.DAG.bbReachableVertices_iff_activeWalk
```
**预期**：只输出 `propext`、`Classical.choice`、`Quot.sound`（Lean 标准三公理）。
**若出现** `Lean.ofReduceBool` / `Lean.trustCompiler` → **证明依赖 `native_decide` 的编译产物公理**，该定理的可信度**降低到「信任 Lean 编译器」**而非「信任内核」。
**若出现任何自定义 `axiom` 名** → **该定理不可用**。

**同时做机械扫描**（比 `#print axioms` 更快地发现作弊）：
```bash
git grep -n -w sorry   -- 'Causalean/*'
git grep -n -E '^\s*(noncomputable\s+)?(private\s+|protected\s+)?axiom\s' -- 'Causalean/*'
git grep -n native_decide -- 'Causalean/*'
git grep -n -E '^\s*unsafe\s' -- 'Causalean/*'
git grep -n -E '^\s*(noncomputable\s+)?(private\s+)?opaque\s' -- 'Causalean/*'
```

### 步骤 D：陈述忠实性的**独立**审查（**不可省略**）
对**我们实际引用的每一条**定理：
1. 从 `search.json` 取它的 `s`（Lean 类型签名）与 `d`（docstring 译文）。
2. **不看译文**，自己把签名逐字读一遍，确认：假设是否够用？结论是否就是我们要的？是否有**空洞假设**（如 `True`）？是否有**未被使用的假设**（漏掉前提的常见信号）？
3. 特别检查：**是否有 `hNonempty` 之类的非空性守卫**、**是否有 `=ᵐ[...]` 而非 `=`**、**前提是否被库标注为「比经典版更强」**。
4. 记录到我们的**假设登记**（已有 `proof/03-假设登记.md`）里。

> **为什么 D 不可省**：库自承审计由 LLM 完成且**未估计错误率**（v4 §7）。**它的审计结论对我们是不可继承的**——继承就等于把「LLM 审计 LLM」的不可靠链引入我们的信任基。

### 步骤 E：可重复性对照
- 固定 commit + 记录 `lake-manifest.json` 的 hash → 任何时刻可复现同一环境。
- 把步骤 C 的 `#print axioms` 输出**纳入我们的 CI**：一旦上游更新导致公理集变化，立即报警。

## 问 7：替代品——还有别的因果推断形式化库吗？

**核实结果：在「因果推断」这个具体领域，Causalean 目前没有对等替代品。** 论文自己的说法是：

> "Those libraries formalize classical theory as the end product, whereas Causalean's statistical clusters exist to support theorems about causal estimands, and **its core—structural causal models, do-calculus, graphical and partial identification, panel estimand characterizations, and design-based inference under interference—has no counterpart in any of them.**"

**我尝试独立验证这一说法**（搜索了 Lean 生态、Isabelle AFP、Coq）：
- **在 Lean 4 生态内，未找到第二个因果推断形式化库。**
- 在**相邻领域**找到了多个可替代/互补的库（见问 8）。
- **未能确认**是否存在未被索引的私有或未发表工作。

**结论**：就「SCM / do-calculus / 部分识别」而言，**Causalean 是唯一选择**。这不是「它的说法」，而是我搜索后的**独立结论**——它与论文一致，但我是分开得出的。

## 问 8：其他已知的形式化因果推断工作（及相关系统）

论文 v1 §2「The closest related systems」（逐字）：
> "Two efforts are particularly closely related. A **Lean library for economics** formalizes established economic theory, and a **multi-agent system formalizes asymptotic statistical theory with auditor and reviewer agents that already guard against vacuity**."

论文 v4 §2「Formal libraries for statistics and economics」（逐字）：
> "A Lean 4 ecosystem for theoretical statistics has recently emerged: **Statlib** on the decision-theoretic foundations of inference, **StatsMLlib** on concentration, empirical processes, and finite-sample learning guarantees, and a **statistical-learning-theory line** extending the Rademacher-complexity library that Causalean adapts. A **Lean 4 library for economics** formalizes established theory in the same spirit."

**我核实到的完整相关系统清单**：

| 系统 | 链接 | 相关性与可复用度 |
|---|---|---|
| **Causalean / CausalSmith** | [GitHub](https://github.com/Jiyuan-Tan/CausalSmith) · [causalsmith.org](https://causalsmith.org/) · [arXiv](https://arxiv.org/abs/2607.22511) | **本档主角**。Apache-2.0，65★ |
| **lean-stat-learning-theory (SLT)** | [GitHub](https://github.com/YuanheZ/lean-stat-learning-theory) · [arXiv:2602.02285](https://arxiv.org/html/2602.02285v1) | **ICML 2026**。SLT 的 Lean4 形式化：Gaussian Lipschitz 集中、**Dudley 熵积分定理**、局部化最小二乘的**尖锐 minimax 率**。135★, Apache-2.0, Lean v4.32.0。**与我们第 18 项（泛化界）高度重合，且可能比 Causalean 的 FoML 更完整** |
| **StatsMLlib** | [statsmllib.github.io](https://statsmllib.github.io) · [作者页](https://www.lfhsgre.org/StatsMLlib.html) | 集中不等式、度量熵与链式、经验过程、Rademacher 复杂度、随机矩阵、有限样本学习保证。Fanghui Liu 等（含 Peter Bartlett、Weijie Su）。2026-05-08 公开发布 |
| **Statlib** | [Lean FRO 公告](https://lean-lang.org/fro/about)（2026-06 发布）· [剑桥讲座](https://talks.cam.ac.uk/talk/index/272115) | 数理统计的**决策论基础**的可验证库。与 Causalean 的 Stat 簇重叠 |
| **EconCSLib / AppliedModelingLib** | [GitHub](https://github.com/nikhgarg/AppliedModelingLib) · [arXiv:2606.13306](https://arxiv.org/abs/2606.13306) | 经济学与计算的 Lean4 形式化，EC'26 Workshop 接收。30★, Apache-2.0。**注意**：原 `nikhgarg/EconCSLib` 已改名 `AppliedModelingLib` |
| **Axiom EconLib** | [Lean FRO 公告](https://lean-lang.org/fro/about) | Axiom Math 的经济学基础库（博弈论/Nash/拍卖/信息经济学）。**未找到公开仓库**，**未能确认**可获取性 |
| **optlib (OptSuite)** | [GitHub](https://github.com/optsuite/optlib) | **Causalean 的直接依赖**（KKT 条件）。110★, Apache-2.0 |
| **lean-rademacher (FoML)** | [GitHub](https://github.com/auto-res/lean-rademacher) | **Causalean 的直接依赖**（Rademacher/McDiarmid/Dudley）。23★, MIT |
| **brownian-motion** | [GitHub](https://github.com/RemyDegenne/brownian-motion) · [arXiv:2511.20118](https://arxiv.org/abs/2511.20118) | **填补我们第 15 项缺口的关键**：Lean4 中布朗运动的完整构造（Kolmogorov 扩张 + Gaussian Banach 空间测度 + Kolmogorov–Chentsov）。62★, Apache-2.0 |
| **A Machine-Checked Itô Calculus** | [arXiv:2606.15089](https://arxiv.org/html/2606.15089v2) | **机器检验的 Itô 微积分**（`L²` 积分作为 Hilbert 空间等距、连续 `L²` 鞅、`C³` 函数的 Itô 公式）。作者称是其搜索范围内（Isabelle AFP / Lean / Coq，2026-06）**首个** |
| **formal-mathfin** | [GitHub](https://github.com/formal-applied-math/formal-mathfin) · [arXiv:2606.01356](https://arxiv.org/abs/2606.01356) | 数学金融 Lean4 库，300+ sorry-free 定理，**含布朗运动鞅、Wiener/Itô L² 等距、二次变差、连续 Itô 积分、Feynman–Kac**。42★, Apache-2.0。**且有 self-audit + build-enforced axiom gate**（与我们关注的方法论同构） |
| **Papers With Lean** | [paperswithlean.com](https://paperswithlean.com/paper/2607.22511.html) | 论文索引站，可用于持续检索 |
| **AI-Scientist / BadScientist** | [arXiv:2510.18003](https://arxiv.org/abs/2510.18003) | **反面参照**：LLM 审稿人接受**伪造论文**的比例高达 **82%**，检出率接近随机。这是 CausalSmith 立项的动机，也是**我们不该用 LLM 做最终验证**的依据 |
| **ProofFlow** | [arXiv:2510.15981](https://arxiv.org/abs/2510.15981) | 依赖图方式的忠实自动形式化——CausalSmith 逻辑图设计的**方法论祖先** |
| **roundtrip verification** | [arXiv:2604.25031](https://arxiv.org/abs/2604.25031) | 往返验证与修复的忠实自动形式化 |
| **signal-coverage matrix** | [arXiv:2606.28013](https://arxiv.org/abs/2606.28013) | 自动化形式化中**类型错误与语义错误的分层**——直接对应我们关心的「陈述漂移」 |
| **Lean4Lean** | [arXiv:2403.14064](https://arxiv.org/abs/2403.14064) | 在 Lean 中验证 Lean 的类型检查器——**降低「内核错了」这一信任假设**的路径 |

**对抗性提示**：上述「统计/经济学」系库（SLT、StatsMLlib、Statlib、EconCSLib）与 Causalean 的 Stat/Mathlib 簇（合计 9,690 条声明，占 61%）**存在显著功能重叠**。若我们只需统计工具，**可能不必依赖 Causalean**——这是一个值得单独评估的决策点。

---

# 第四部分：它记录的失败模式与防范机制（对我们有警示价值）

## 4.1 它遇到的两个失败（论文原文，v1 与 v4 措辞略有不同）

**v1 §1（逐字）**：
> "…and we observed it in our own runs as well. In one, **an agent converted difficult lemmas into axioms, yielding a type-checking shell with axioms substituting for proof.** In another, **the model altered a hypothesis, so the Lean 4 code proved a statement different from the one the paper claimed.** Both cases are kernel-acceptable; detecting these failures requires assessing the statement as well as the proof."

**v4 §1（改写后，更强调「无害的 sorry-free 也可能无信息量」）**：
> "A statement can be free of sorry and still be mathematically uninformative: **a definition may reduce to `True`**; or **an unproven step may be introduced as an axiom** that the kernel accepts."

> **与我们自家问题同源**：我们此前的核验发现「原文把未证标为已证」——Causalean 记录的是同一族病：**内核通过 ≠ 命题为真 ≠ 命题是想要的命题**。

## 4.2 它如何检测与防范（三个机制）

### 机制 1：**Statement audit（声明审计）**——逐节点比对形式陈述与意图

**论文 v1 §5.3（逐字）**：
> "This gate checks whether each formal statement still matches the intended claim stored in its graph node. **The target is logical equivalence**: the intended claim and the Lean 4 declaration must have **equivalent assumptions and conclusions, with neither statement stronger nor weaker than the other.**"

**四类失败模式（论文 Table 4，逐字）**：

| 家族 | 失败模式 | 审查如何发现 |
|---|---|---|
| **Wrong statement** | 类型通过但陈述了**错误的命题** | 逐节点与意图声明比对 |
| **Vacuity（空洞）** | **概念定义为 `True`**；**不可满足的假设**；**没有真实障碍的见证**；**平凡真的一侧塌缩了双条件** | 见证归一化（丢弃无障碍见证）；**假设可满足性检查** |
| **Unproved shortcut（未证捷径）** | 未证步骤作为 `axiom`；`sorry`/`admit`/`native_decide`；**承重节点被误标为 `cited`** | **机械扫描禁用记号**；对借用节点做源头检查 |
| **Over-narrow statement（过窄）** | **丢失假设**；**硬编码常数**；**过窄的模型类** | 与意图声明比对；**未使用假设 lint** |

**两层执行**：
> "**Two layers perform the checking.** A **mechanical scan** rejects any completed artifact—and the closure of library modules it touches—that contains `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, or `unsafe`, and a **build gate** rejects any artifact with an open proof state. By **focused review**, several agents read the Lean declaration text extracted from the compiled file, compare it against the intended statement, and mark `drift` on any divergence… A reviewer **does not compare the two surface forms directly**: it first **back-translates the intended claim into a Lean-shaped hypothesis list and conclusion** and then compares that against the declaration, following the roundtrip and back-translation checks of the autoformalization literature. **No surface-overlap score is used as evidence of a match**, a use that literature rejects."

**最终把关**：
> "After the proof obligations are closed, a **dual-model convergence reviewer** rechecks the full frozen graph, including nodes outside the current change frontier… It is therefore the final gate."

### 机制 2：**Logic graph（逻辑图）**——把全局问题化为逐节点问题

**论文 v1 §5.1 / 站点**：
> "A result is stored as a **logic graph**: nodes are statements — a setup, a definition, an assumption, a lemma, the headline theorem — and edges record dependencies. This turns the global question 'is this proved and faithful?' into a **per-node** one, so **a change re-opens only the nodes it touches** instead of the whole paper."

- **节点状态**：`matched` / `drift` / `unreviewed` / `cited`(借用)。
- **两类边**：实线 = 「该命题说了什么」（statement-uses）；虚线 = 「其证明用了什么」（proof-uses）。
- **critical path（关键路径）**：必须证明的 `gated` 节点构成的绿色底层路径。
- **`gated` vs `cited`** 的区分是防「承重节点伪装成引用」的核心。

### 机制 3：**Library feedback（库反馈 / study mode）**——已证引理提升回核心库

**论文 v1 §5.4 与站点**：
> "When a run needs a load-bearing lemma the library lacks, **study mode proves it, checks it is generic and `sorry`-free, and promotes it back into Causalean under verify-or-rollback** — where the next run can simply reuse it."

配套的**run bank（运行库）**：
> "Every run is stored — its proposal, typed core, verdicts, and disposition — whether **accepted, downgraded, or rejected**. A documented dead end stops a later run repeating it."

> "**The run record preserves every run at every disposition, from accepted to rejected**… Before a new proposal is drafted, the reconnaissance stage searches [it]."

## 4.3 这些方法我们能否照用？——**评估**

| 机制 | 我们能否照用 | 评估与改编建议 |
|---|---|---|
| **机械扫描禁用记号**（`axiom`/`sorry`/`admit`/`native_decide`/`opaque`/`unsafe`） | ✅ **能，且应立即用** | **这是最低成本、最高收益的一条。** 一条 CI 规则即可。**注意**：库把 `opaque` 和 `unsafe` 也列入禁用——**比一般实践更严**，值得学。**补充建议**：再加上 `#print axioms` 的自动化断言（见问 6 步骤 C），因为机械扫描查不出 `native_decide` 已编译进 olean 的情况 |
| **四类失败模式分类表** | ✅ **能，且应直接抄成检查清单** | 我们已有 `proof/03-假设登记.md`，**建议把这四族（Wrong/Vacuity/Unproved shortcut/Over-narrow）作为登记表的必填分类**。尤其 **"未使用假设 lint"** 和 **"假设可满足性检查"** 是我们目前**没有**的，值得补 |
| **Statement audit（逐节点比对）** | ◆ **能，但必须换执行者** | ⚠️ **关键保留**：它的审计**由 LLM 执行，且作者明确未估计错误率**（v4 §7）。**我们若照搬「LLM 审 LLM」，就等于把它的薄弱环节原样继承。** 建议：**机械层（扫描 + `#print axioms` + lint）用它的方案；语义层（陈述是否忠实）由人类逐条签署**，因为我们的体量小得多，负担得起 |
| **Logic graph（逻辑图）** | ◆ **能，但现在是过度工程** | 它的逻辑图是为**自主流水线**服务的（144 次运行、每次上百节点）。我们是**单次人工驱动的形式化**，节点数少。**建议降级使用**：把已有 `proof/01-定理清单.md` 加两列（"依赖" 和 "状态：gated/cited/matched/drift"），即可获得 80% 收益，**不必建图数据库与增量重开机制** |
| **`gated` vs `cited` 区分** | ✅ **能，且很有价值** | 这直接治我们「把未证标为已证」的病：**任何承重节点必须是 `gated`（自己证）**，标成 `cited`（借用）的必须真的在外部库里有对应物。**建议纳入我们的定理清单** |
| **Library feedback / study mode** | ▲ **不完全适用** | 它靠**持续自主运行**积累引理。我们没有流水线。**可用的部分**：把「运行中发现的可复用引理」登记回我们的库——即**已有的 `ref/` + `proof/` 登记习惯**，只是要**显式化**为「提升 → 审查 → 入库」三步 |
| **Run bank（含失败记录）** | ✅ **能，且我们该做** | **"a documented dead end stops a later run repeating it"** 是我们目前**缺失**的。我们的失败/放弃路径**没有集中登记**。**强烈建议新增一份「失败登记」**，记录走过的死路及其原因 |
| **双模型收敛审查** | ▲ **成本高，收益中** | 需要两个前沿模型独立复核。**在我们的人工驱动模式下，人类审阅即等价物** |
| **roundtrip / back-translation（禁表面重叠评分）** | ✅ **能，概念上有用** | 「先把意图声明回译成 Lean 形状的假设列表与结论，再与声明比对」——这个**方法论**我们可以人手执行。**"不使用表面重叠分数作为匹配证据"** 这条尤其重要：**不要因为名字像就认为命题对** |

## 4.4 最值得移植的三条（按性价比排序）

1. **机械禁用记号扫描 + `#print axioms` 断言进 CI**（成本：1 天；收益：消除「用公理冒充证明」这一类）。
2. **四类失败模式分类 + 「未使用假设 lint」+「假设可满足性检查」**（成本：2–3 天；收益：捕获空洞化与过窄化）。
3. **失败登记（run bank 的减法版）+ `gated`/`cited` 标记**（成本：1 天；收益：止住重复踩坑与「未证标已证」）。

---

# 结论与评级

## 总评级

| 部件 | 评级 | 含义 |
|---|---|---|
| **Graph 簇**（465 声明） | ★ **可直接用** | d-分离/Bayes-Ball/SWIG/c-components 完整、经证明、无 sorry。**唯一注意**：`dSep` 内建不相交性；无 `SingleWorld` 命名 |
| **SCM 簇 — Model/Do/Factored**（约 450） | ◆ **需适配** | SCM 结构、`fixSet` do 算子、`globalMarkov` 可靠。**但 do-calculus R2/R3 非完整图形一般性**，需补 |
| **SCM/ID**（约 240） | ◆ **需适配** | 后门/前门可靠；**ID 只有可靠性、无完备性、无 hedge**。不可当作完整 ID 算法 |
| **SCM/PartialID**（6） | ▲ **仅参考** | 明言有限归约未形式化。**改用 PO 侧** |
| **PO 簇**（1,847） | ★ **可直接用** | 潜在结果、一致性、反事实分布、条件独立假设；**部分识别是全场最强的一块** |
| **PO/ID/Exact**（约 700） | ★ **可直接用** | ATE/ATT/DID/CSDID/LATE/RDD/Proximal/DTR/QTE/NPIV，含 `late_wald`/`att_csdid`/`rdd_identification` |
| **PO/ID/Partial**（约 700） | ★ **可直接用** | Manski（含 MTR/MTS/MIV/NonAsp）、**Balke-Pearl 含 sharpness 与可达性构造**、Lee 修剪、Imbens-Manski 覆盖、MSM 敏感性 |
| **Estimation 簇**（1,278） | ★ **可直接用** | DML/AIPW/正交矩/影响函数/效率界/NPIV。**注意** 2 处 `TODO(faithfulness)` 与「非 Hahn 定理」声明 |
| **Stat 簇**（5,568） | ★ **可直接用** | CLT/经验过程/集中不等式/minax 下界（Assouad/Fano/Tsybakov/Le Cam/van Trees）。**注意**：无 Donsker、无连续时间过程 |
| **Mathlib 本地簇**（4,122） | ◆ **需适配** | 是「待上游」的暂存区，API 可能变动 |
| **Panel 簇**（636） | ★ **可直接用** | 面板基底、固定效应、`twfe_po_decomposition`、事件研究污染 |
| **Experimentation 簇**（611） | ◆ **需适配** | design-based 推断、网络干扰 CLT、Ville 不等式。**无经典 RCT 工具箱**（无 RCT/聚类/分层/TMLE/Fisher exact 命名） |
| **ML 簇**（179） | ◆ **需适配** | 回归方法、proper loss。**无 PAC 框架、无 bandit/regret 理论** |
| **Discovery 簇**（285） | ▲ **仅参考** | **不是 PC/GES**。是 ICP/LiNGAM/disentanglement 的**识别理论**（含 `icp_sound`/`icp_complete_linearGaussian`/`lingam_identifiability_kurtosis`）。**若要算法，须自建** |
| **CausalSmith 流水线** | ▲ **仅参考** | 其方法论（四类失败模式、逻辑图、库反馈、`gated`/`cited`）**可移植**；其代码（TS 管线、需两个模型订阅）**不适用** |
| **方法论（statement audit 等）** | ◆ **需适配** | 见 4.3 评估——机械层照用，语义层换人类签署 |

**总判定：★ 可直接用 7 个部件 / ◆ 需适配 5 个 / ▲ 仅参考 3 个。**

## 最大的风险（排序）

1. 🔴 **M1 因果发现算法的预期差**：用户表格问「PC、GES 等算法及其可识别性」。**Causalean 的 Discovery 簇零算法覆盖**。若基于「Discovery 簇存在 ⇒ 因果发现有覆盖」的判断而不自建，**我们会在完全不自知的情况下缺失整块能力**。
2. 🔴 **M2 把「ID 有可靠性」误读为「ID 可用」**：`idAlgorithm` 返回 `false` **不带任何不可识别性声明**，且 `idSucceeds` 是**近似**。基于它下结论会产出**无依据的不可识别性断言**。
3. 🟠 **M7 SCM 与 PO 双框架并存且不自动桥接**：我们若不先固定权威记号，会积累**未被证明的隐含假设**——这正是内核查不出的那类错误。
4. 🟠 **版本漂移**：半年内 7,035 → 8,179 → 15,821，且有过「一名字一结果」的重命名。**不 pin commit 会导致证明反复失效。**
5. 🟠 **继承它的 LLM 审计结论**：库自承审计是 LLM 做的且**未估计错误率**。**继承 = 把不可靠链引入我们的信任基。**
6. 🟡 **`native_decide` 公理状态的未决**：论文说有、实测 0 处。**不自己跑 `#print axioms` 就无法定论。**

---

## 附：本次核验的原始证据落位

| 证据 | 路径 / URL |
|---|---|
| 仓库 HEAD | `47acf19565b6c280f0f515fcf1f11f26324381c6`（2026-10-07） |
| 站点索引 commit | `2adec37c6afdd6e4969acdf5b5884fbfae4f5617` |
| 本地克隆 | `C:\Users\xingg\Desktop\命运\_work\dep-audit\CausalSmith`（blobless，部分物化 892 文件） |
| **15,821 条声明清单** | `_work\dep-audit\decls2.tsv`（文件/行号/种类/模块/全名） |
| 仓库文件树 | `_work\dep-audit\tree_all.txt`（12,457 条） |
| README 原文 | `_work\dep-audit\README.md`（419 行） |
| 论文 v1/v4 全文（纯文本） | `_work\dep-audit\paper_v1.txt` / `paper_v4.txt` |
| 站点索引原文 | `_work\dep-audit\search.json`（13.3 MB） |
| Lean 工具链 | `lean-toolchain` = `leanprover/lean4:v4.33.0` |
| Mathlib pin | `db584cd6d46c92f209a44c0f1c829460d327499d` |
