# T-4：namespace 不匹配诊断（**只诊断，未修改任何 `.lean`**）

> 生成方式：只读扫描 `/root/fate-dev/Fate/*.lean`（798 个 `.lean` 文件），
> 辅以 `lake env lean` 实测抽检。**本任务未修改任何 `.lean` 文件。**

---

## 0. 结论先行（TL;DR）

**这不是 bug，是刻意的「组件命名空间 / umbrella namespace」设计。**

- `Fate/GraphToProbView7.lean` 建立了一个**命名空间载体**，后续 **25 个文件**（`TailBlock*`、`CondIndep*`、`Balance*`、`ArrowEquivA`…）都进
  `namespace Fate.GraphToProbView7` 往同一个数学主题里**追加**定理。文件名是「章节名」，namespace 是「主题名」——两者本来就不该相等。
- 下游代码**确实按 namespace 名引用**（`Fate.GraphToProbView7.condIndep_general` 等共 67 处），并且**编译通过**。
- 实测 `#check` / `import` 均零报错，说明当前状态是**自洽**的。

**但是**：确有 **1 个真实的隐性冲突**（`Fate.FactorRecursionRouteB.pa_subset_nonDescendants`
被两个文件重复声明，见 §6.1），目前靠「下游各自改写成本地名」绕开，属于**随时会踩的雷**。

**任务书里的「141 个」与脚本「301」、严格口径「321」都对不上**，见 §1.1。本报告按**实测的 321 / 301 两个口径**给出完整清单。

---

## 1. 完整统计（可复核）

### 1.1 数字口径说明（重要，先纠正基线）

| 口径 | 计数 | 说明 |
|---|---|---|
| 任务书正文宣称 | **141** | ❌ 无法复现。任务书自带脚本跑出来不是 141。 |
| 任务书脚本原样运行 | **301** | 判据 `any(文件名 in ns)`（**子串**匹配） |
| 本报告严格口径 | **321** | 判据：文件名 ≠ 任一 namespace 的**最后一段**（含 15 个无 namespace 文件） |

两个口径的差集恰好 20 个，全部是「文件名只出现在 namespace 的**中间段**」的，例如

- `ErrorBound.lean` → `namespace Fate.R250ErrorBound`（`ErrorBound` 是 `R250ErrorBound` 的子串）
- `KernelQuotient.lean` → `namespace Fate.KernelQuotientTheory`
- `RuleLevel.lean` → `namespace Fate.RuleLevelAlias`
- `SupportBound.lean` → `namespace Fate.R_SupportBound`
- `ZipDownFalse.lean` → `namespace Fate.ZipDownFalseFixed`
- 以及 15 个**完全没有 namespace** 的 `.lean`（`BridgeKernel`、`LMGcCoverGap`…，见 §4-D）

**⟹ 任务书里「141」这个数字无出处，不采信。** 本报告以实测 301/321 为基线。

### 1.2 按「namespace 末段」的分布（前 12）

| namespace 末段 | 文件数 |
|---|---|
| `Fate`（只写了顶层 `namespace Fate`，没更细的） | 31 |
| `Fate.GenN` | 27 |
| `Fate.GraphToProbView7` | 24 |
| `FormalCtx` | 15 |
| `LawRule` | 10 |
| `SCM` / `AlphaData` / `Fate.View19` / `Fate.T21` | 各 3–5 |
| `AudUniv2` / `Consumer` / `FactorRecursionRouteB` … | 各 2 |

### 1.3 共享命名空间规模（证明「umbrella」是主流用法）

| namespace | 使用它的文件数 |
|---|---|
| `Fate` | **517** |
| `Fate.GraphToProbView7` | **25** |
| `Fate.GenN` | **27**（+1 个裸 `GenN`） |
| `FormalCtx` | 19 |
| `LawRule` | 15 |
| `RuleSyntax` | 8 |
| `WorldScenario` / `SCM` / `Exec` | 各 6 |

> 「一个 namespace 被十几个文件填」在本库是**常态**，不是异常。

---

## 2. 分类（A / B / C / D）

| 类 | 计数 | 含义 | 合法？ |
|---|---|---|---|
| **A** | **38** | 通用「生成/组件」命名空间：`Gen*`、`Step*`、`Consumer`、`Demo`、`Fixed`、`Setup*`、`Tight` | ✅ 合法 |
| **B-umbrella** | **134** | 末段是**另一个真实文件名**，但该 namespace 被 **≥2 文件共享**（= 主题 umbrella） | ✅ 合法（设计） |
| **B-单例** | **6** | 末段是其它真实文件名，且**只有本文件**用该 namespace | ⚠️ 需逐个看（见 §5） |
| **C** | **128** | 内部代号命名空间：`C5e`、`C15`、`C18`、`S9Fixed`、`R277`、`T21`、`W7`、`Bal2` … | ✅ 合法（代号即身份） |
| **D** | **15** | **完全没有 namespace**（纯 note / 纯声明文件） | ✅ 合法 |

> 注：B-umbrella 与 C 的边界是启发式的（按正则 + 共享文件数）。个别条目的归类可与报告不同，但**不影响 §6 结论**。

完整 321 行清单见 **附录 A**（按 A → B-umbrella → B-单例 → C → D 排序，附每个 namespace 的共享文件数）。

---

## 3. B 类抽样验证（5 个，附下游引用证据）

任务书要求「抽 5 个 B 类，grep 它的定理在其他模块里怎么被引用」。这里挑任务书**点名的** 5 个：

### 3.1 `BalanceComponents.lean` → `namespace Fate.GraphToProbView7`

- 它定义的 `card_balance` 在**全库被引用 19 处**（排除自身），如
  `BalanceFactorPart.lean:16` 明确写「该文件的 §0.1 `card_balance` 只给了指数层面的基数恒等式」。
- 下游 `BalanceFactorPart.lean` 同样在 `Fate.GraphToProbView7` 下，**裸名调用**。
- `Fate.GraphToProbView7.*` 全库被引用 **67 处**。
- ⟹ 命名空间是**共享主题**，合法。

### 3.2 `TailBlockCondIndep.lean` → `namespace Fate.GraphToProbView7`

**最硬的证据**：`TailBlockAssemble.lean`
```
1: import Fate.TailBlockCondIndep     ← 导入它
25: namespace Fate.GraphToProbView7   ← 进同一个 namespace
102: have hCondA := condIndep_on_A ... ← 裸名调用它定义的定理
```
如果 `TailBlockCondIndep` 的 namespace 改成文件名，第 102 行的**裸名调用会直接 fail**。
⟹ 两个文件必须同 namespace 才能编译。**合法，且是强耦合的刻意设计。**

### 3.3 `ArrowEquivA.lean` → `namespace Fate.GraphToProbView7`

- 定义 `arrowEquivA` / `arrowEquivA_fst` / `card_tail`。
- 被 `MassADecompFinal.lean`（同样 `namespace Fate.GraphToProbView7`）在
  第 56、64、66、76 行**裸名**使用：`rw [← Equiv.sum_comp (arrowEquivA A) ...]`。
- 全库 `arrowEquivA` 引用 29 处（排除自身）。
- ⟹ 合法。

### 3.4 `NaryAlgebra.lean` → `namespace Fate.GenC3`

- `CondIndepN.lean:67` 是 `namespace GenC3`（在 `Fate` 下），`NaryAlgebra.lean:28` 是 `namespace Fate.GenC3` —— **同一命名空间的两个写法**。
- `Fate.GenC3.*` 全库被引用 **46 处**（`Fate.GenC3.CondIndepN`、`Fate.GenC3.NJoint`、`Fate.GenC3.marg` …）。
- ⟹ 合法（由 `Nary*` 系列共享的 N 元层命名空间，`GenC3` 是「三次生成 / Gen-C3」代号）。

### 3.5 `MassFactorOfReads.lean` → `namespace Fate.C5e`

- 定义 `mass_factor_of_reads`。
- 下游 `MassIndepOfCompl.lean:208` **按 namespace 名**引用：
  `Fate.C5e.mass_factor_of_reads (A := A) (C := C) (Z := Z) ...`
- 该行**能编译**（已随全库构建验证），证明 `C5e` 是真实存在的命名空间。
- 文件头把 `C5e` 当作「组件编号」使用（同类的还有 `C5b/C5d/C5f/C5g/C5h/C5i`，各自一个文件）。
- ⟹ 合法（**代号命名空间**，与任务书的「C 类」定义吻合，即使按 B 类判据被抓到）。

> **额外**：`BarCorrected.lean` → `Fate.S9Fixed` 被下游引用 4 处；`MassAEqCorrected.lean` → `Fate.C6b` 被引用 0 处（孤立文件，命名无所谓）。均编译通过。

---

## 4. D 类：15 个「无 namespace」文件（合法）

```
BridgeKernel, ExistingToolsAudit, LMGcCoverGap, LMGcCoverObstacle,
LMGcDirectRoute, LMGcFinalVerdict, LMGcProjectionNote, LMGcRouteHistory,
NoCoverCondIndepPlan, RouteBGapNote, SinkPeelDiagnosis, SinkPeelFinalVerdict,
SolutionCLMGcNote, SubMassPlan, TwoRoutesNote
```
从名字看全是 `*Note` / `*Diagnosis` / `*Verdict` / `*Plan` 类**纯文档 / 纯陈述文件**（很多连定理都没有）。放在 `Fate` 顶层命名空间外是合理的。

---

## 5. B-单例：6 个需要单独确认的

这 6 个的 namespace 末段是「另一个真实文件名」，且**该 namespace 只有本文件用**。逐个核实：

### 5.1 `AlphaKernelAudit.lean` → `Fate.AlphaKernel` ✅ 合法

文件头自述：`Fate.AlphaKernelAudit  =====================  **审计问题**：α 是否保持了抽象等价（AlphaKernel 里的核）？`
它是 `AlphaKernel` 的**审计章节**：`Fate.AlphaKernel.alphaKernel` 被下游按名引用（1 处，`AlphaKernelAudit.lean:29` 表格）。
**同一数学对象的审计 → 放同一命名空间**，合法。且文件 **0 sorry**。

### 5.2 `TailFromDSepFork.lean` → `Fate.TailFromDSep` ⚠️ 合法但含 1 个 sorry
`TailFromDSep` 这个名字**不**出现在文件名列表里？——实际核查：`grep` 只在 `TailFromDSepFork.lean` / `TailFromDSepIntegration.lean` 命中，说明是「Fork/Integration 两个子文件共用 `Fate.TailFromDSep` 主题 ns」。合法。**但该文件含 1 处 `sorry`**（本任务只读，未改动）。

### 5.3 `LawRulePointDecidabilityConsumer.lean` → `Fate.PointDecidabilityConsumer` ⚠️ 合法但含 1 个 sorry
`PointDecidabilityConsumer` 是 `LawRule` 子模块的细分 ns（`NonemptyFree2.lean` 也用）。合法。**含 1 处 sorry**。

### 5.4 `LawRuleRuleBridge.lean` → `Fate.RuleBridgeComb` / `RuleBridgeInstances` / `RuleBridgeSeq` ✅ 合法
一个文件里开了 **3 个**「桥接」子命名空间（组合 / 实例 / 序列），是**文件内分层**，每个只本文件用。合法。**0 sorry**。

### 5.5 `RuleActivationClosureOp.lean` → `Fate.RuleReadSetBridge` ✅ 合法
文件内再开一个「读集桥」子 ns。合法。**0 sorry**。

### 5.6 `GhostAliases.lean` → `Fate.View19` / `Fate.GraphToProbView7` / `Fate.FactorizesToHyper` / `Fate.CondIndepCondMulBridge`
从名字看是**别名 / 转发文件**，一次性在多个既有命名空间中登记 alias。`Fate.CondIndepCondMulBridge.*` 被下游引用 3 处且编译通过。合法。**0 sorry**。

> **⟹ 6 个 B-单例全部是「文件内分层 / 审计章节 / 别名登记」，没有一个是无意的笔误。**
> 只有 `TailFromDSepFork` 与 `LawRulePointDecidabilityConsumer` 各含 1 个 `sorry`（与 namespace 无关，属另一问题）。

---

## 6. 真实隐患（不是 namespace 不匹配，但由共享 ns 引入）

### 6.1 ⚠️ 重复声明：`Fate.FactorRecursionRouteB.pa_subset_nonDescendants`

两个文件**在同一个 namespace 下声明了同名定理**：

| 文件 | 行 | 声明 |
|---|---|---|
| `FactorRecursionRouteB_Obligations.lean` | 48 | `theorem pa_subset_nonDescendants (G) (v) : pa G v ⊆ G.nonDescendants v` |
| `G1ParentNonDescendant.lean` | 67 | `theorem pa_subset_nonDescendants (G) (v) : pa G v ⊆ G.nonDescendants v` |

而 `Fate.lean`（根模块）**同时导入了两者**（第 476、482 行）。

**实测**（Lean 4.33.0-rc1）：
- 最小复现 `dup_a.lean` / `dup_b.lean` 都写 `namespace Foo; theorem bar`，`import` 时**确实报错**：
  `error: import dup_b failed, environment already contains 'Foo.bar' from dup_a`
- 但真实文件 `import Fate.FactorRecursionRouteB_Obligations` + `import Fate.G1ParentNonDescendant` **零报错**，
  `#check @pa_subset_nonDescendants` 能解析，`#print axioms` 正常。

**⟹ 判断**：当前 Lean 构建下**没炸**（可能因为 `.olean` 构建顺序或 module 私有化细节），但这是**语义上两套同名定义**：
下游 `BridgeA2.lean:253` 用的是 `Fate.FactorRecursionRouteB.pa_subset_nonDescendants`，而 `ViewTenThreeBlock.lean:37` 也用它；
`BridgeA1.lean:86` 干脆**在 `Fate.BridgeA1` 下又写了一份本地副本**并让全家改用它（`Fate.BridgeA1.pa_subset_nonDescendants`）。
`BridgeA1` 的这一处置本身就是「作者已感知到同名冲突」的证据。

**⟹ 这是本任务中唯一具有「真 bug 潜力」的发现**，但**不是** namespace 与文件名不匹配导致的，而是**两个文件抢占同一 namespace 内的同一名字**。

### 6.2 「裸名 vs 全名」双写法
`GenN` / `GenC3` / `GraphToProbView7` 都有**两种写法混用**：
`namespace GenN`（裸，1 个文件）与 `namespace Fate.GenN`（6 个文件）；`namespace GenC3`（裸）与 `namespace Fate.GenC3`（1 个）。
只要外层有 `namespace Fate` 包着，两者等价；若某文件漏了外层 `namespace Fate`，裸名就会落到**顶层** `GenN`，与 `Fate.GenN` 变成**两个不同命名空间**。抽样未见实际踩雷，但这是隐患。

---

## 7. 结论

| 问题 | 回答 |
|---|---|
| 这 300+ 个不匹配是 bug 吗？ | **绝大多数不是。** 是「主题包围命名空间（umbrella ns）」设计：文件名=章节，namespace=数学主题。 |
| 下游按哪个名字引用？ | **按 namespace 名**（`Fate.GraphToProbView7.condIndep_general`、`Fate.C5e.mass_factor_of_reads`、`Fate.GenC3.*` 等），且**编译通过**。 |
| 是真 bug 还是历史遗留？ | **历史遗留 + 刻意设计。** 唯一「真 bug 潜力」是 §6.1 的重复声明。 |
| 应否修？ | **不建议现在改。** 见 §8。 |

---

## 8. 建议（**不改代码，仅建议**）

1. **不要**把这些 namespace 改成文件名。
   `TailBlockAssemble.lean:102` 的裸名 `condIndep_on_A`、`MassADecompFinal.lean:56` 的裸名 `arrowEquivA`
   都依赖「同 namespace」。改名会**连锁打断**至少 67 处 `Fate.GraphToProbView7.*` 引用 + 46 处 `Fate.GenC3.*`。
   本库已通过构建，改名的收益（可读性）远小于风险（破坏 3 次构建的历史教训）。

2. **只修 §6.1 的重复声明**（这是唯一实质问题）。二选一：
   - 方案 A（最小侵入）：把 `G1ParentNonDescendant.lean` 里 `pa_subset_nonDescendants` 改名为
     `pa_subset_nonDescendants_G1`（或加 `private`），并同步它内部的 2 处自引用（第 87、90 行附近）。
   - 方案 B（更彻底）：保留一份，删掉另一份，让下游统一指向 `Fate.FactorRecursionRouteB.pa_subset_nonDescendants`。
     注意 `BridgeA1.lean` 已有一份本地副本，需一并评估是否删除。

3. **统一裸名 / 全名写法**（§6.2）：把 `namespace GenN` / `namespace GenC3` 统一改成 `namespace Fate.GenN` / `Fate.GenC3`（前提：外层确有 `namespace Fate`）。纯机械替换，低风险。

4. **若只想「可搜性」**：在 `Fate.lean` 里为每个 umbrella ns 加**别名注释**（不改代码），或在 `_audit/` 维护「文件名 ↔ namespace」对照表（本报告附录 A 即为此表），避免后来者误判。

5. **不要在报告里说「141 个」**——实测 301（子串口径）/ 321（严格口径）。建议把本报告 §1.1 作为新的基线。

---

## 附录 A：完整清单（321 条）

> 分类说明：`A` = 通用生成名；`B-umbrella` = 末段是真实文件名但 ≥2 文件共享；`B-单例` = 末段是真实文件名且仅本文件用；`C` = 内部代号；`D` = 无 namespace。
> 「该 ns 共享文件数」= 全库有多少个 `.lean` 用了这个 namespace（>1 即证明是刻意共享）。

| # | 文件 | namespace（按出现序） | 分类 | 理由 | 该 ns 共享文件数 |
|---|---|---|---|---|---|
| 1 | `BridgeEquiv.lean` | `Fate`<br>`GenC2` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>GenC2:1 |
| 2 | `BridgeView2Elimination.lean` | `Fate.BridgeView2`<br>`Demo` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.BridgeView2:1<br>Demo:2 |
| 3 | `CondIndepN.lean` | `Fate`<br>`GenC3` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>GenC3:1 |
| 4 | `GammaOperator.lean` | `Fate`<br>`GenOp`<br>`FormalCtx`<br>`RuleSpec` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>GenOp:1<br>FormalCtx:19<br>RuleSpec:1 |
| 5 | `InterventionTight.lean` | `Fate`<br>`WorldScenario`<br>`Tight`<br>`Fate.WorldScenario.Tight` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>WorldScenario:6<br>Tight:1<br>Fate.WorldScenario.Tight:1 |
| 6 | `MassOfReadsCover.lean` | `Fate.Direct` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.Direct:1 |
| 7 | `NKernelValue.lean` | `Fate`<br>`GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>GenN:1 |
| 8 | `NaryAlgebra.lean` | `Fate.GenC3` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenC3:1 |
| 9 | `NaryAssembly.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 10 | `NaryBridge.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 11 | `NaryBridgeDone.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 12 | `NaryBridgeFinal.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 13 | `NaryBridgeMulti.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 14 | `NaryCancel.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 15 | `NaryClose.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 16 | `NaryConnect.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 17 | `NaryConnect2.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 18 | `NaryConnect3.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 19 | `NaryFiberDecomp.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 20 | `NaryFin2.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 21 | `NaryFinal.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 22 | `NaryFinalBridge.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 23 | `NaryGeneric.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 24 | `NaryIndex.lean` | `Fate.GenN`<br>`Fate.GenN`<br>`Fate.GenN`<br>`Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27<br>Fate.GenN:27<br>Fate.GenN:27<br>Fate.GenN:27 |
| 25 | `NaryIndexCheck.lean` | `Fate.GenN`<br>`Fate.GenN`<br>`Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27<br>Fate.GenN:27<br>Fate.GenN:27 |
| 26 | `NaryKernel.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 27 | `NaryKernel2.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 28 | `NaryLink.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 29 | `NaryMargSum.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 30 | `NaryMassLink.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 31 | `NaryMeasure.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 32 | `NaryPointwise.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 33 | `NaryProduct.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 34 | `NaryRealSum.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 35 | `NaryTrim.lean` | `Fate.GenN` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.GenN:27 |
| 36 | `RegressStep9Fiber.lean` | `Fate.Step9R1` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate.Step9R1:1 |
| 37 | `RuleSyntaxGen.lean` | `Fate`<br>`RuleSyntax`<br>`Gen` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>RuleSyntax:8<br>Gen:1 |
| 38 | `RuleSyntaxGenOps.lean` | `Fate`<br>`RuleSyntax`<br>`GenOps` | A | 通用生成/组件命名空间(Gen*/Step*/...)，多文件共享 | Fate:517<br>RuleSyntax:8<br>GenOps:1 |
| 39 | `ActInputDecomp.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 40 | `Adjudication.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 41 | `Adjunction.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 42 | `Alpha.lean` | `Fate`<br>`FormalCtx`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19<br>FormalCtx:19 |
| 43 | `AlphaAndStochasticWiringConsumer.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 44 | `AlphaConcreteInstance.lean` | `Fate`<br>`AlphaInstance` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaInstance:5 |
| 45 | `AlphaDataConsumed.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 46 | `AlphaDataToLawRule.lean` | `Fate`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3 |
| 47 | `AlphaDataToPartition.lean` | `Fate`<br>`AlphaData` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaData:3 |
| 48 | `AlphaFCAConstruction.lean` | `Fate`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData`<br>`AlphaData` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3<br>AlphaData:3 |
| 49 | `AlphaFourOp.lean` | `Fate`<br>`AlphaInstance`<br>`WiringFixed` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaInstance:5<br>WiringFixed:3 |
| 50 | `AlphaFourOpConsumer.lean` | `Fate`<br>`AlphaInstance`<br>`WiringFixed` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaInstance:5<br>WiringFixed:3 |
| 51 | `AlphaOf.lean` | `Fate`<br>`AlphaMVFCA` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>AlphaMVFCA:4 |
| 52 | `AlphaRulesLocal.lean` | `Fate`<br>`AlphaMVFCA` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>AlphaMVFCA:4 |
| 53 | `ArrowEquivA.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 54 | `AudUnivLayer2.lean` | `Fate`<br>`AudUniv2` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AudUniv2:2 |
| 55 | `AudUnivLayer2b.lean` | `Fate`<br>`AudUniv2` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AudUniv2:2 |
| 56 | `BalanceComponents.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 57 | `BalanceFactorPart.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 58 | `Basic.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 59 | `BridgeDirectConsumer.lean` | `Fate.BridgeDirect` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.BridgeDirect:2 |
| 60 | `BridgeReverse.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 61 | `BridgeSingleFiber.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 62 | `CausalOnWorldModelAdjust.lean` | `Fate`<br>`CausalOnWorldModel` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>CausalOnWorldModel:2 |
| 63 | `CellDiameter.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 64 | `CfPartialIdentConsumer.lean` | `Fate`<br>`CfPartialIdent` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>CfPartialIdent:2 |
| 65 | `Classification.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 66 | `Compactness.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 67 | `Completeness.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 68 | `ConceptLatticeComplete.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 69 | `CondIndepEmptyZ.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 70 | `CondIndepGeneralNZ.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 71 | `DAGFactorizationGeneral.lean` | `Fate`<br>`DAGFactorization`<br>`Fate`<br>`DAGFactorization` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>DAGFactorization:2<br>Fate:517<br>DAGFactorization:2 |
| 72 | `DetFunToStep.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 73 | `DetFunToStepDraft.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 74 | `EvaluationSystemsConsumer.lean` | `Fate`<br>`EvaluationSystems`<br>`Consumer` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>EvaluationSystems:2<br>Consumer:2 |
| 75 | `FCA.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 76 | `FactorRecursionRouteB_Obligations.lean` | `Fate`<br>`FactorRecursionRouteB` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>FactorRecursionRouteB:3 |
| 77 | `FactorizesOnComponents.lean` | `Fate.T1A2Substance` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.T1A2Substance:2 |
| 78 | `FactorizesToCondMul.lean` | `Fate`<br>`FinMarkov` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>FinMarkov:2 |
| 79 | `Frame.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 80 | `G1ParentNonDescendant.lean` | `Fate`<br>`FactorRecursionRouteB` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>FactorRecursionRouteB:3 |
| 81 | `GaloisEmbedding.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 82 | `GazeAlgebraConsumer.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 83 | `GlobalMarkovChainNConsumer.lean` | `Fate`<br>`GlobalMarkovChainN`<br>`Consumer` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>GlobalMarkovChainN:2<br>Consumer:2 |
| 84 | `GuardNecessary.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 85 | `Implication.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 86 | `InstIsDirac.lean` | `Fate`<br>`LawRuleInstances` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRuleInstances:2 |
| 87 | `KahnTopo.lean` | `Causalean.Graph` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Causalean.Graph:2 |
| 88 | `KernelQuotient.lean` | `Fate`<br>`KernelQuotientTheory` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>KernelQuotientTheory:2 |
| 89 | `KernelQuotientExtra.lean` | `Fate`<br>`KernelQuotientTheory` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>KernelQuotientTheory:2 |
| 90 | `LawDetToStepGen.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 91 | `LawRuleAlgebraUnify.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 92 | `LawRuleLattice.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 93 | `LawRuleMarginal.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 94 | `LawRulePointDecidability.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 95 | `LawRuleSatisfiability.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 96 | `LawRuleSequence.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 97 | `LawRuleUnion.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 98 | `LoopBoundReal.lean` | `Fate.MainLoop` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.MainLoop:3 |
| 99 | `MVFCAClosure.lean` | `MVFCA4`<br>`PatStruct` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | MVFCA4:2<br>PatStruct:2 |
| 100 | `MVFCAFinset.lean` | `Fate`<br>`AlphaMVFCA`<br>`FcaToRuleTerm` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>AlphaMVFCA:4<br>FcaToRuleTerm:2 |
| 101 | `MVFCAPositive.lean` | `MVFCA4`<br>`PatStruct` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | MVFCA4:2<br>PatStruct:2 |
| 102 | `MacroShiftsMicro.lean` | `Fate`<br>`CausalEventFormal` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>CausalEventFormal:2 |
| 103 | `MainTheoremC.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 104 | `MainTheoremCFinal.lean` | `Fate.GraphToProbView7`<br>`Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25 |
| 105 | `MarginSizeIrrelevant.lean` | `Fate.MainLoop` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.MainLoop:3 |
| 106 | `MassADecompFinal.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 107 | `MassProCover.lean` | `Fate.View19` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.View19:4 |
| 108 | `Minimality.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 109 | `ObsEstimationStrong.lean` | `Fate`<br>`RA14Strong` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>RA14Strong:2 |
| 110 | `PathDepIsDerived.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 111 | `PathDependence.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 112 | `PearlJointLaw.lean` | `Fate`<br>`PearlHierarchy` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>PearlHierarchy:3 |
| 113 | `PearlLawRuleBridge.lean` | `Fate`<br>`PearlHierarchy`<br>`PearlHierarchy`<br>`SCM` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>PearlHierarchy:3<br>PearlHierarchy:3<br>SCM:6 |
| 114 | `PearlPathDecomp.lean` | `Fate`<br>`CausalPath` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>CausalPath:2 |
| 115 | `PipelineTendstoSpecializes.lean` | `Fate`<br>`WorldModelPipeline` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>WorldModelPipeline:2 |
| 116 | `PolicyAlgorithm.lean` | `Fate`<br>`WorldScenario` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>WorldScenario:6 |
| 117 | `ProdSplitSides.lean` | `Fate.View19` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.View19:4 |
| 118 | `RebaseSplit.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 119 | `ResidualReducesInj.lean` | `Fate`<br>`ResidualReduces` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>ResidualReduces:2 |
| 120 | `RoundtripAsymmetry.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 121 | `RuleActivationClosureOpConsumer.lean` | `Fate`<br>`RuleActivation` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>RuleActivation:3 |
| 122 | `RuleDrivesEndToEnd.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 123 | `RuleExec.lean` | `Fate`<br>`RuleSyntax`<br>`Exec` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>RuleSyntax:8<br>Exec:6 |
| 124 | `RuleSimConsistency.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 125 | `SCMLawBridge.lean` | `Fate`<br>`LawRule`<br>`SCM` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15<br>SCM:6 |
| 126 | `SCMLawBridgeAdvance.lean` | `Fate`<br>`LawRule`<br>`SCM` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15<br>SCM:6 |
| 127 | `Satisfiability.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 128 | `SetupXMYDemo.lean` | `Fate.SetupXMY`<br>`DemoX` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.SetupXMY:3<br>DemoX:2 |
| 129 | `SetupXMYDemoLaw.lean` | `Fate.SetupXMY`<br>`DemoX` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.SetupXMY:3<br>DemoX:2 |
| 130 | `Stage1A.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 131 | `StatAlphaConsumer.lean` | `Fate`<br>`StatAlpha` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>StatAlpha:2 |
| 132 | `StepToLaw.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 133 | `StepToLawDraft.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 134 | `StepToLawGenFiber.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 135 | `Strategy13Filler.lean` | `Fate.Strategy13` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.Strategy13:2 |
| 136 | `Strategy13TypedSplit.lean` | `Fate.Strategy13` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.Strategy13:2 |
| 137 | `SumMulSep.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 138 | `SumMulSepFull.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 139 | `SumSeparation.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 140 | `SynClosureBounded.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 141 | `SynClosureSemiNaive.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 142 | `T112FCAPolar.lean` | `Fate`<br>`FormalCtx` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>FormalCtx:19 |
| 143 | `T51Trajectory.lean` | `Fate.MainlineTheorems` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.MainlineTheorems:3 |
| 144 | `T611Full.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 145 | `T611FullConsumer.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 146 | `T65QuotientOp.lean` | `Fate.MainlineTheorems` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.MainlineTheorems:3 |
| 147 | `TailBlockAssemble.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 148 | `TailBlockBridge.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 149 | `TailBlockCondIndep.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 150 | `TailBlockIntegration.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 151 | `TailBlockMassDcomp.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 152 | `TailBlockMassDecomp.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 153 | `TailBlockReal.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 154 | `TailBlockReal2.lean` | `Fate.GraphToProbView7`<br>`Fate.GraphToProbView7`<br>`Fate.GraphToProbView7`<br>`Fate.GraphToProbView7`<br>`Fate.GraphToProbView7`<br>`Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25 |
| 155 | `TailBlockReal2Consumer.lean` | `Fate.GraphToProbView7`<br>`Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25<br>Fate.GraphToProbView7:25 |
| 156 | `TailFromDSep.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 157 | `TailOutExtract.lean` | `Fate.View19` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.View19:4 |
| 158 | `TailTailCollapse.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 159 | `TailVerdict.lean` | `Fate.GraphToProbView7` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate.GraphToProbView7:25 |
| 160 | `TermSize.lean` | `Fate`<br>`RuleSyntax`<br>`Exec` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>RuleSyntax:8<br>Exec:6 |
| 161 | `TrajGenStochastic.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 162 | `UpsilonRefine.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 163 | `VarsigmaScale.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 164 | `VersionSpace.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 165 | `VersionSpaceBoundary.lean` | `Fate`<br>`LawRule` | B-umbrella | 末段=另一个真实文件名，且该 namespace 被≥2文件共享 | Fate:517<br>LawRule:15 |
| 166 | `View3AtomStratification.lean` | `Fate.View3` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate.View3:2 |
| 167 | `WiringFourOpFixed.lean` | `Fate`<br>`AlphaInstance`<br>`WiringFixed`<br>`Step` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>AlphaInstance:5<br>WiringFixed:3<br>Step:2 |
| 168 | `WorldModel.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 169 | `WorldModelCompleteV2.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 170 | `WorldModelCompleteV2NonDeg.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 171 | `WorldModelCompleteV2W.lean` | `Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517 |
| 172 | `WorldModelNoPredict.lean` | `Fate`<br>`Fate` | B-umbrella | 末段=其它真实文件名，namespace被多文件共享 | Fate:517<br>Fate:517 |
| 173 | `AlphaKernelAudit.lean` | `Fate.AlphaKernel` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate.AlphaKernel:1 |
| 174 | `GhostAliases.lean` | `Fate.View19`<br>`Fate.GraphToProbView7`<br>`Fate.FactorizesToHyper`<br>`Fate.CondIndepCondMulBridge` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate.View19:4<br>Fate.GraphToProbView7:25<br>Fate.FactorizesToHyper:1<br>Fate.CondIndepCondMulBridge:1 |
| 175 | `LawRulePointDecidabilityConsumer.lean` | `Fate`<br>`LawRule`<br>`PointDecidabilityConsumer` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate:517<br>LawRule:15<br>PointDecidabilityConsumer:1 |
| 176 | `LawRuleRuleBridge.lean` | `Fate`<br>`LawRule`<br>`RuleBridgeComb`<br>`RuleBridgeInstances`<br>`RuleBridgeSeq` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate:517<br>LawRule:15<br>RuleBridgeComb:1<br>RuleBridgeInstances:1<br>RuleBridgeSeq:1 |
| 177 | `RuleActivationClosureOp.lean` | `Fate`<br>`RuleActivation`<br>`Fate`<br>`RuleActivation`<br>`RuleReadSetBridge` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate:517<br>RuleActivation:3<br>Fate:517<br>RuleActivation:3<br>RuleReadSetBridge:1 |
| 178 | `TailFromDSepFork.lean` | `Fate`<br>`TailFromDSep` | B-单例 | 末段=另一个真实文件名，但该 namespace 仅本文件使用 | Fate:517<br>TailFromDSep:1 |
| 179 | `AlgoKNNComponents.lean` | `KNNComponents`<br>`IsConnectedPartition` | C | 其它名字，仅本文件 | KNNComponents:1<br>IsConnectedPartition:1 |
| 180 | `AlphaAndStochasticWiring.lean` | `Fate`<br>`AlphaDataOfInstances` | C | 其它名字，仅本文件 | Fate:517<br>AlphaDataOfInstances:1 |
| 181 | `BackdoorAdjustment.lean` | `Fate.Backdoor` | C | 其它名字，仅本文件 | Fate.Backdoor:1 |
| 182 | `BackdoorCriterion.lean` | `Fate.R259`<br>`BackdoorSetup`<br>`BackdoorSetup`<br>`Fate.R259`<br>`Fate.R259.Demo`<br>`Fate.R259.Demo`<br>`Fate.R259.Demo`<br>`Fate.R259.Demo`<br>`Fate.R259.BadOpen`<br>`GraphCheck` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R259:1<br>BackdoorSetup:2<br>BackdoorSetup:2<br>Fate.R259:1<br>Fate.R259.Demo:1<br>Fate.R259.Demo:1<br>Fate.R259.Demo:1<br>Fate.R259.Demo:1<br>Fate.R259.BadOpen:1<br>GraphCheck:2 |
| 183 | `BackdoorFiber.lean` | `Fate.R229` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R229:1 |
| 184 | `BackdoorGenuine.lean` | `Fate.R277`<br>`BackdoorSetup`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277`<br>`Fate.R277` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R277:2<br>BackdoorSetup:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2<br>Fate.R277:2 |
| 185 | `BackdoorWithM.lean` | `Fate.R289`<br>`SetupWithM`<br>`SetupWithM`<br>`SetupWithM`<br>`SetupWithM`<br>`SetupWithM`<br>`SetupWithM`<br>`Demo`<br>`Bad`<br>`Evidence` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R289:1<br>SetupWithM:1<br>SetupWithM:1<br>SetupWithM:1<br>SetupWithM:1<br>SetupWithM:1<br>SetupWithM:1<br>Demo:2<br>Bad:1<br>Evidence:1 |
| 186 | `BarCorrected.lean` | `Fate.S9Fixed` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.S9Fixed:1 |
| 187 | `BarSdiffEq.lean` | `Fate.C15` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C15:1 |
| 188 | `BarSdiffIndep.lean` | `Fate.C18` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C18:1 |
| 189 | `BlockCIFactorization.lean` | `Fate.C5h` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5h:1 |
| 190 | `BlockCIGeneralC.lean` | `Fate.C5g` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5g:1 |
| 191 | `BlockCIOfBlockSplit.lean` | `Fate.C5b` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5b:1 |
| 192 | `BlockCIOfBlockSplitFinal.lean` | `Fate.C5f` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5f:1 |
| 193 | `BlockCIUltimate.lean` | `Fate.C5i` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5i:1 |
| 194 | `BridgeFinal.lean` | `Fate`<br>`FinalB3`<br>`Fate`<br>`FinalB3` | C | 其它名字，仅本文件 | Fate:517<br>FinalB3:1<br>Fate:517<br>FinalB3:1 |
| 195 | `BridgeStrategy1TopoPeel.lean` | `Fate`<br>`BridgeStrategy1`<br>`Counterexample` | C | 其它名字，仅本文件 | Fate:517<br>BridgeStrategy1:1<br>Counterexample:3 |
| 196 | `BridgeStrategy4CoordSlice.lean` | `Fate`<br>`BridgeStrategy4` | C | 其它名字，仅本文件 | Fate:517<br>BridgeStrategy4:1 |
| 197 | `BridgeStrategy5FiberBijection.lean` | `Fate`<br>`BridgeStrategy5` | C | 其它名字，仅本文件 | Fate:517<br>BridgeStrategy5:1 |
| 198 | `BridgeView3AtomStratification.lean` | `Fate.BridgeView3` | C | 其它名字，仅本文件 | Fate.BridgeView3:1 |
| 199 | `BridgeView9EdgeKernel.lean` | `Fate`<br>`BridgeView9`<br>`EdgeKernel` | C | 其它名字，仅本文件 | Fate:517<br>BridgeView9:1<br>EdgeKernel:1 |
| 200 | `BridgeView9EdgeKernelConsumer.lean` | `Fate`<br>`BridgeView9Consumer` | C | 其它名字，仅本文件 | Fate:517<br>BridgeView9Consumer:1 |
| 201 | `CardBalanceLMGc.lean` | `Fate.Bal2` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.Bal2:1 |
| 202 | `CausalFCADSep.lean` | `Fate`<br>`DSepFCA` | C | 其它名字，仅本文件 | Fate:517<br>DSepFCA:1 |
| 203 | `ChainMarkovInductive.lean` | `Fate.ChainInductive` | C | 其它名字，仅本文件 | Fate.ChainInductive:1 |
| 204 | `ColliderDAGValues.lean` | `Fate.BridgeA4Fixed4` | C | 其它名字，仅本文件 | Fate.BridgeA4Fixed4:1 |
| 205 | `ColliderPValues.lean` | `Fate.BridgeA4Fixed2` | C | 其它名字，仅本文件 | Fate.BridgeA4Fixed2:1 |
| 206 | `CondIndepContraction.lean` | `Fate`<br>`Contraction` | C | 其它名字，仅本文件 | Fate:517<br>Contraction:1 |
| 207 | `CondIndepIntersection.lean` | `Fate`<br>`Intersection` | C | 其它名字，仅本文件 | Fate:517<br>Intersection:1 |
| 208 | `CondIndepSemigraphoid.lean` | `Fate`<br>`Semigraphoid` | C | 其它名字，仅本文件 | Fate:517<br>Semigraphoid:1 |
| 209 | `DSepCondNonMonotone.lean` | `Causalean.Graph`<br>`DAG` | C | 其它名字，仅本文件 | Causalean.Graph:2<br>DAG:1 |
| 210 | `DoSemanticsBridge.lean` | `Fate.DoSemantics` | C | 其它名字，仅本文件 | Fate.DoSemantics:1 |
| 211 | `ErrorBound.lean` | `Fate`<br>`R250ErrorBound` | C | 其它名字，仅本文件 | Fate:517<br>R250ErrorBound:1 |
| 212 | `ErrorBoundChain.lean` | `Fate`<br>`R253ErrorBound`<br>`Fate`<br>`R253ErrorBound` | C | 其它名字，仅本文件 | Fate:517<br>R253ErrorBound:1<br>Fate:517<br>R253ErrorBound:1 |
| 213 | `ErrorGraph.lean` | `Fate`<br>`ErrGraph` | C | 其它名字，仅本文件 | Fate:517<br>ErrGraph:1 |
| 214 | `FactorizesNotImpliesLMG.lean` | `Fate.Witness` | C | 其它名字，仅本文件 | Fate.Witness:1 |
| 215 | `FitBoundary.lean` | `Fate`<br>`R238E3`<br>`ErrProfileWeak`<br>`ErrProfile` | C | 其它名字，仅本文件 | Fate:517<br>R238E3:1<br>ErrProfileWeak:1<br>ErrProfile:1 |
| 216 | `FourNodeSeparation.lean` | `FourNode` | C | 其它名字，仅本文件 | FourNode:1 |
| 217 | `FrontdoorChainProof.lean` | `Fate.R242` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R242:1 |
| 218 | `FrontdoorCounterexample.lean` | `Fate.R253` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R253:1 |
| 219 | `FrontdoorCounterexample2.lean` | `Fate.R254` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R254:1 |
| 220 | `FrontdoorCriterion.lean` | `Fate.R255`<br>`FrontdoorSetup`<br>`Fate.R255.R32` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R255:1<br>FrontdoorSetup:1<br>Fate.R255.R32:1 |
| 221 | `H5AdjudicationK.lean` | `Fate`<br>`H5K` | C | 其它名字，仅本文件 | Fate:517<br>H5K:1 |
| 222 | `LMGcCondIndepEquiv.lean` | `Fate.LMGCEquiv` | C | 其它名字，仅本文件 | Fate.LMGCEquiv:1 |
| 223 | `MainLoopSupportBridge.lean` | `Fate`<br>`MainLoopSupport` | C | 其它名字，仅本文件 | Fate:517<br>MainLoopSupport:1 |
| 224 | `MassAEqCorrected.lean` | `Fate.C6b` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C6b:1 |
| 225 | `MassBoundaryValues.lean` | `Fate.C7` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C7:1 |
| 226 | `MassFactorOfReads.lean` | `Fate.C5e` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5e:1 |
| 227 | `MassIndepOfCompl.lean` | `Fate.C17`<br>`Fate.R17Mass` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C17:1<br>Fate.R17Mass:1 |
| 228 | `MassInsertCorrected.lean` | `Fate.S13HoistFixed` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.S13HoistFixed:1 |
| 229 | `MassMultSBridge.lean` | `Fate.C8` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C8:1 |
| 230 | `MassSdiffConst.lean` | `Fate.C11` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C11:1 |
| 231 | `MultSUnify.lean` | `Fate.C6c` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C6c:1 |
| 232 | `NonDescendantsMem.lean` | `Fate.NDMem` | C | 其它名字，仅本文件 | Fate.NDMem:1 |
| 233 | `NotLMGColliderP.lean` | `Fate.BridgeA4Fixed3` | C | 其它名字，仅本文件 | Fate.BridgeA4Fixed3:1 |
| 234 | `ObsEstimationStrongG4Link.lean` | `Fate`<br>`RA14Strong`<br>`G4Link` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>RA14Strong:2<br>G4Link:1 |
| 235 | `OptimalityThirdInstance.lean` | `Fate`<br>`FitExpThirdInstance`<br>`InterventionNegative`<br>`FitWNegative` | C | 其它名字，仅本文件 | Fate:517<br>FitExpThirdInstance:1<br>InterventionNegative:1<br>FitWNegative:1 |
| 236 | `PearlChain.lean` | `Fate`<br>`P213B1` | C | 其它名字，仅本文件 | Fate:517<br>P213B1:1 |
| 237 | `PearlFork.lean` | `Fate`<br>`Fork213` | C | 其它名字，仅本文件 | Fate:517<br>Fork213:1 |
| 238 | `PearlMarkovBridgeG1.lean` | `Fate`<br>`R242G1` | C | 其它名字，仅本文件 | Fate:517<br>R242G1:1 |
| 239 | `Rule13Genuine.lean` | `Fate`<br>`R249`<br>`Exog`<br>`Rule1`<br>`Rule3`<br>`Rule1`<br>`Rule3` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>R249:1<br>Exog:1<br>Rule1:1<br>Rule3:1<br>Rule1:1<br>Rule3:1 |
| 240 | `Rule13GenuineConsumer.lean` | `Fate`<br>`R740`<br>`R1`<br>`R3`<br>`Cross`<br>`Bridge` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>R740:1<br>R1:1<br>R3:1<br>Cross:1<br>Bridge:2 |
| 241 | `Rule1Genuine.lean` | `Fate`<br>`R1G`<br>`ZSCM`<br>`ZSCM`<br>`ZSCM`<br>`ZSCM`<br>`MgoodProof`<br>`MdetProof`<br>`ZSCM`<br>`MbadProof`<br>`Graph`<br>`Tables` | C | 其它名字，仅本文件 | Fate:517<br>R1G:1<br>ZSCM:1<br>ZSCM:1<br>ZSCM:1<br>ZSCM:1<br>MgoodProof:1<br>MdetProof:1<br>ZSCM:1<br>MbadProof:1<br>Graph:1<br>Tables:1 |
| 242 | `Rule1Semantic.lean` | `Fate`<br>`R242G3`<br>`SCM` | C | 其它名字，仅本文件 | Fate:517<br>R242G3:1<br>SCM:6 |
| 243 | `Rule23Semantic.lean` | `Fate`<br>`R246G3`<br>`Sem3` | C | 其它名字，仅本文件 | Fate:517<br>R246G3:1<br>Sem3:1 |
| 244 | `Rule2Genuine.lean` | `Fate`<br>`R248`<br>`Sem`<br>`Sem`<br>`Sem`<br>`Sem`<br>`GraphCheck`<br>`Bridge`<br>`Bridge` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>R248:1<br>Sem:1<br>Sem:1<br>Sem:1<br>Sem:1<br>GraphCheck:2<br>Bridge:2<br>Bridge:2 |
| 245 | `RuleEvaluation.lean` | `Fate`<br>`RuleEval` | C | 其它名字，仅本文件 | Fate:517<br>RuleEval:1 |
| 246 | `RuleLevel.lean` | `Fate`<br>`RuleLevelAlias` | C | 其它名字，仅本文件 | Fate:517<br>RuleLevelAlias:1 |
| 247 | `ScottContinuity.lean` | `Fate`<br>`FormalCtx`<br>`Kbad` | C | 其它名字，仅本文件 | Fate:517<br>FormalCtx:19<br>Kbad:1 |
| 248 | `ScratchAssemblyLearns.lean` | `Fate`<br>`AssemblyLearnsScratch` | C | 其它名字，仅本文件 | Fate:517<br>AssemblyLearnsScratch:1 |
| 249 | `SdiffEraseEq.lean` | `Fate.C14` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C14:1 |
| 250 | `SetupXMYDemoLawConsumer.lean` | `Fate.SetupXMY.DemoX` | C | 其它名字，仅本文件 | Fate.SetupXMY.DemoX:1 |
| 251 | `SinkPeelCounterexample.lean` | `Fate.C9` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C9:1 |
| 252 | `SinkPeelGeneralRefutation.lean` | `Fate.C19` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C19:1 |
| 253 | `SolutionCLMGcCounterexample.lean` | `Fate.GapCE` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.GapCE:1 |
| 254 | `Strategy11AncestralHull.lean` | `Fate.Strategy11Hull` | C | 其它名字，仅本文件 | Fate.Strategy11Hull:1 |
| 255 | `Strategy11FiberPinned.lean` | `Fate.Strategy11Fiber` | C | 其它名字，仅本文件 | Fate.Strategy11Fiber:1 |
| 256 | `Strategy11TopoPrefix.lean` | `Fate.Strategy11` | C | 其它名字，仅本文件 | Fate.Strategy11:1 |
| 257 | `Strategy12FactorSplitBridge.lean` | `Fate.Strategy12` | C | 其它名字，仅本文件 | Fate.Strategy12:1 |
| 258 | `Strategy13FactorHoist.lean` | `Fate.Strategy13Hoist` | C | 其它名字，仅本文件 | Fate.Strategy13Hoist:1 |
| 259 | `Strategy13FiberFubini.lean` | `Fate.Strategy13Fubini` | C | 其它名字，仅本文件 | Fate.Strategy13Fubini:1 |
| 260 | `Strategy9SinkPeelNorm.lean` | `Fate`<br>`Strategy9Norm` | C | 其它名字，仅本文件 | Fate:517<br>Strategy9Norm:1 |
| 261 | `Strategy9SinkPeelVerdict.lean` | `Fate`<br>`Strategy9Verdict` | C | 其它名字，仅本文件 | Fate:517<br>Strategy9Verdict:1 |
| 262 | `Strategy9TopoLayerTruncation.lean` | `Fate`<br>`Strategy9` | C | 其它名字，仅本文件 | Fate:517<br>Strategy9:1 |
| 263 | `SubFibCard.lean` | `Fate.C5d` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.C5d:1 |
| 264 | `SubMassFoundations.lean` | `Fate.Block2` | C | 其它名字，仅本文件 | Fate.Block2:1 |
| 265 | `SupportBound.lean` | `Fate`<br>`R_SupportBound`<br>`SuppProfile` | C | 其它名字，仅本文件 | Fate:517<br>R_SupportBound:1<br>SuppProfile:1 |
| 266 | `T04NotationFidelity.lean` | `Fate.T04` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T04:1 |
| 267 | `T111QuotientPred.lean` | `Fate.T111` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T111:1 |
| 268 | `T112Candidates.lean` | `Fate`<br>`C1`<br>`C2`<br>`C3`<br>`C4`<br>`C5` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>C1:1<br>C2:1<br>C3:1<br>C4:1<br>C5:1 |
| 269 | `T112Exactly.lean` | `Fate`<br>`AuditA`<br>`AuditD`<br>`AuditC`<br>`Fate`<br>`R11T112` | C | 其它名字，仅本文件 | Fate:517<br>AuditA:1<br>AuditD:1<br>AuditC:1<br>Fate:517<br>R11T112:1 |
| 270 | `T112FCAConnection.lean` | `Fate.T112` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T112:2 |
| 271 | `T112FCASpecific.lean` | `Fate`<br>`FormalCtx`<br>`ClosureSep`<br>`NonSelfDual`<br>`NonSelfDual`<br>`RankTwo`<br>`Contrast`<br>`Counterexample` | C | 其它名字，仅本文件 | Fate:517<br>FormalCtx:19<br>ClosureSep:1<br>NonSelfDual:2<br>NonSelfDual:2<br>RankTwo:2<br>Contrast:1<br>Counterexample:3 |
| 272 | `T112FCASpecific2.lean` | `Fate`<br>`Meta`<br>`Separator1`<br>`Separator2`<br>`Separator3` | C | 其它名字，仅本文件 | Fate:517<br>Meta:1<br>Separator1:1<br>Separator2:1<br>Separator3:1 |
| 273 | `T112FCATheorems.lean` | `Fate`<br>`ThmA`<br>`ThmC`<br>`ThmD`<br>`ThmE` | C | 其它名字，仅本文件 | Fate:517<br>ThmA:1<br>ThmC:1<br>ThmD:1<br>ThmE:1 |
| 274 | `T112SecondQuotient.lean` | `Fate.T112` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T112:2 |
| 275 | `T112UnaryClosure.lean` | `Fate`<br>`T112Unary`<br>`T112Arb` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>T112Unary:1<br>T112Arb:1 |
| 276 | `T21DSepWellDefined.lean` | `Fate.T21` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T21:3 |
| 277 | `T21Decidable.lean` | `Fate.T21` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T21:3 |
| 278 | `T21FiniteSearch.lean` | `Fate.T21` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T21:3 |
| 279 | `T21FiniteSearchConsumer.lean` | `Fate.T21Consumer` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T21Consumer:1 |
| 280 | `T314Identifiability.lean` | `Fate.T314` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T314:1 |
| 281 | `T33DoGraph.lean` | `Fate`<br>`R230`<br>`VecSCM` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>R230:1<br>VecSCM:1 |
| 282 | `T34DoPushforward.lean` | `Fate.T34` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T34:1 |
| 283 | `T35Confounding.lean` | `Fate.T35` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T35:1 |
| 284 | `T43Abduction.lean` | `Fate`<br>`T43` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>T43:1 |
| 285 | `T43CounterfactualAbduction.lean` | `Fate.R242.G2` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.R242.G2:1 |
| 286 | `T44Counterfactual.lean` | `Fate.T44`<br>`SCM` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T44:1<br>SCM:6 |
| 287 | `T61MapKernel.lean` | `Fate.T61` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate.T61:1 |
| 288 | `T68ComposeSemantics.lean` | `Fate.R230B4` | C | 其它名字，仅本文件 | Fate.R230B4:1 |
| 289 | `T810PrMaj.lean` | `Fate`<br>`PrMaj` | C | 其它名字，仅本文件 | Fate:517<br>PrMaj:1 |
| 290 | `TwoVersions.lean` | `Fate`<br>`BoundWriteBackV2` | C | 其它名字，仅本文件 | Fate:517<br>BoundWriteBackV2:1 |
| 291 | `View10AdmissibleReach.lean` | `Fate.View10` | C | 其它名字，仅本文件 | Fate.View10:1 |
| 292 | `View11SplitterChain.lean` | `Fate`<br>`View11Splitter` | C | 其它名字，仅本文件 | Fate:517<br>View11Splitter:1 |
| 293 | `View14CutReweight.lean` | `Fate.View14` | C | 其它名字，仅本文件 | Fate.View14:1 |
| 294 | `View15KernelSeparation.lean` | `Fate`<br>`View15` | C | 其它名字，仅本文件 | Fate:517<br>View15:1 |
| 295 | `View16PotentialTransport.lean` | `Fate`<br>`View16` | C | 其它名字，仅本文件 | Fate:517<br>View16:1 |
| 296 | `View18BayesBallBlock.lean` | `Fate`<br>`View18` | C | 其它名字，仅本文件 | Fate:517<br>View18:1 |
| 297 | `View19FactorGraphSplit.lean` | `Fate`<br>`View19` | C | 其它名字，仅本文件 | Fate:517<br>View19:1 |
| 298 | `View20GraphToProb.lean` | `Fate`<br>`View20` | C | 其它名字，仅本文件 | Fate:517<br>View20:1 |
| 299 | `View21StableBorder.lean` | `Fate.View21` | C | 其它名字，仅本文件 | Fate.View21:1 |
| 300 | `View3FiberMassBridge.lean` | `Fate`<br>`View3FiberMass` | C | 其它名字，仅本文件 | Fate:517<br>View3FiberMass:1 |
| 301 | `ViewTenThreeBlock.lean` | `Fate.ViewTen`<br>`Fate.ViewTen`<br>`Fate.ViewTen` | C | 其它名字，仅本文件 | Fate.ViewTen:1<br>Fate.ViewTen:1<br>Fate.ViewTen:1 |
| 302 | `WiringDoCalcFixed.lean` | `Fate`<br>`W7`<br>`Exec`<br>`Exec`<br>`Exec`<br>`Run`<br>`Exec`<br>`DirectBad` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>W7:2<br>Exec:6<br>Exec:6<br>Exec:6<br>Run:1<br>Exec:6<br>DirectBad:1 |
| 303 | `WiringDoCalcFixedConsumer.lean` | `Fate`<br>`W7`<br>`Consume` | C | 内部代号命名空间(C*/S*/R*/T*...) | Fate:517<br>W7:2<br>Consume:1 |
| 304 | `WiringFourOperators.lean` | `Fate`<br>`AlphaInstance`<br>`Wiring`<br>`Step` | C | 其它名字，仅本文件 | Fate:517<br>AlphaInstance:5<br>Wiring:1<br>Step:2 |
| 305 | `ZPrimeDSepRelation.lean` | `Fate.ZPrimeDSep` | C | 其它名字，仅本文件 | Fate.ZPrimeDSep:1 |
| 306 | `ZipDownFalse.lean` | `Fate.ZipDownFalseFixed` | C | 其它名字，仅本文件 | Fate.ZipDownFalseFixed:1 |
| 307 | `BridgeKernel.lean` | (无) | D | 无 namespace | - |
| 308 | `ExistingToolsAudit.lean` | (无) | D | 无 namespace | - |
| 309 | `LMGcCoverGap.lean` | (无) | D | 无 namespace | - |
| 310 | `LMGcCoverObstacle.lean` | (无) | D | 无 namespace | - |
| 311 | `LMGcDirectRoute.lean` | (无) | D | 无 namespace | - |
| 312 | `LMGcFinalVerdict.lean` | (无) | D | 无 namespace | - |
| 313 | `LMGcProjectionNote.lean` | (无) | D | 无 namespace | - |
| 314 | `LMGcRouteHistory.lean` | (无) | D | 无 namespace | - |
| 315 | `NoCoverCondIndepPlan.lean` | (无) | D | 无 namespace | - |
| 316 | `RouteBGapNote.lean` | (无) | D | 无 namespace | - |
| 317 | `SinkPeelDiagnosis.lean` | (无) | D | 无 namespace | - |
| 318 | `SinkPeelFinalVerdict.lean` | (无) | D | 无 namespace | - |
| 319 | `SolutionCLMGcNote.lean` | (无) | D | 无 namespace | - |
| 320 | `SubMassPlan.lean` | (无) | D | 无 namespace | - |
| 321 | `TwoRoutesNote.lean` | (无) | D | 无 namespace | - |

---

## 附录 B：无法验证 / 存疑项（如实登记）

1. **任务书的「141」**：无法用任何脚本口径复现（实测 301 / 321）。已在本报告开头纠正。
2. **§6.1 为什么 Lean 没报错**：最小复现会报 `environment already contains`，但真实两文件导入不报。
   可能原因：`.olean` 构建的 module 私有化 / 导入顺序；**未深挖到 Lean 内部哈希机制**，如实标注为**未完全定论**。
3. **分类的 A/B-umbrella/B-单例/C 边界是启发式的**（正则 + 共享文件数），个别条目可争议；不影响 §7 结论。
4. **任务书给的示例 `Strategy13FiberFubini → Fate.Strategy13Fubini`**：核查为**代号命名空间**（`Strategy13` 系列 4 个文件共用前缀），合法。
5. **`TailFromDSepFork` / `LawRulePointDecidabilityConsumer`** 各含 **1 处 `sorry`**（本任务只读，未改动，未另查其性质）。

---

## 附录 C：本次未做的事（遵守纪律）

- ❌ 未修改任何 `.lean` 文件
- ❌ 未建临时 `.lean`
- ❌ 未跑 `lake build`（全量）
- ✅ 只写了 `_audit/T4-namespace诊断.md` 一个文件
- ✅ 抽检使用的 `/tmp/*.lean` 均在 `/tmp`，**不在 `Fate/` 目录内**

### 重要说明：并发 edit 观察

诊断期间（04:30–04:43）发现 `Fate/` 下有**其它进程/agent 正在并发写 `.lean`**
（`PearlPathDecomp.lean` 被追加 §7、`InterventionSelection.lean`/`SigmaLandscape.lean`/`ThetaMatters.lean` 等被改）。
**这些改动都不是本任务做的**。本任务对 `Fate/` 的写操作为 **0**。
若 §1 的统计数字与后来者重跑不一致，请以「诊断时点的快照」理解——
因为库在被别人同时修改，**快照本身就带时间戳**。
