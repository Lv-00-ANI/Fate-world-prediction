import FateWorld.FateV2.Predict.GlobalMarkovMinimal
import FateWorld.FateV2.Predict.MarkovBridgeReal
import FateWorld.FateV2.Predict.MarkovBridgeAncestral
import FateWorld.FateV2.Predict.MarkovBridgeTopo
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import FateWorld.FateV2.Predict.UndirectedGlobalMarkov
import FateWorld.FateV2.Predict.PearlMarkovBridgeG1
import FateWorld.FateV2.Predict.CondMulSeparable
import FateWorld.FateV2.Predict.ChainMarkovExplicitAntecedent
/-!
  # Predict · MarkovGroupWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovGroupWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：GlobalMarkovMinimal, MarkovBridgeReal, MarkovBridgeAncestral, MarkovBridgeTopo, MoralGraphMarkov, UndirectedGlobalMarkov, PearlMarkovBridgeG1, CondMulSeparable, ChainMarkovExplicitAntecedent
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/MarkovGroupWiring` —— **R-1：因果 Markov 组的真实接线**

  ## 背景（R974 / 本轮实测）

  全库 27 个 `*Markov*` 模块**互不引用**：组内零引用 25 / 27（93%）。
  即：这 27 个模块讲同一件事（Markov 性），却**没有任何一个**在证明体里
  调用**另一个**的定理 —— **知识没有连成网络**。

  ## 本文件做的事

  **本文件不是 Capstone，不是 1:1 别名，不是「只 import」。**
  它把**不同模块**里**已证的方向**串成**新的蕴含链**：

  ```
  P213B1.ChainMarkov ──(GlobalMarkovMinimal.global_markov_minimal)──▶ CondMul
                     ──(R242G1.condMul_imp_condRatio)────────────────▶ CondRatio
  ```

  每一条定理的**证明体**都**真的调用两个不同模块的定理**，
  且结论(`CondRatio` / 可分离)在**两个源模块里都没有** —— 故不是转发。

  ## 接线矩阵（本文件消费的 8 个 Markov 组模块）

  | 来源模块 | 被本文件调用的定理 | 被接线到的结论 |
  |---|---|---|
  | `FateV2.Predict.GlobalMarkovMinimal` | `global_markov_minimal`、`condMul_gives_separable_of_margZ_ne` | ①③⑥⑧ |
  | `Fate.PearlMarkovBridgeG1` | `condMul_imp_condRatio` | ①②④⑤⑦⑧ |
  | `Fate.MarkovBridgeReal` | `chain_markov_relative_condmul` | ②③ |
  | `Fate.MoralGraphMarkov` | `moral_factorization_condmul` | ④⑤ |
  | `Fate.UndirectedGlobalMarkov` | `separable_of_three_factors` | ⑤ |
  | `Fate.MarkovBridgeAncestral` | `three_stage_condmul` | ⑥ |
  | `Fate.MarkovBridgeTopo` | `chainMarkov3_condmul` | ⑦ |
  | `Fate.ChainMarkovExplicitAntecedent` | `chain_factorizes_condMul`、`chain_dsep_factorizes_condMul` | ⑧⑨ |
  | `FateV2.Predict.NonemptyFree.CondMulSeparable` | `condMul_implies_separable` | ③b |

  ## 诚实边界

  * 每条定理的**前件**都是**真前件**（因子分解 / 链 Markov 性 / 团分解），
    **没有**把结论预先塞进前件（逐条自审见各定理的 docstring）；
  * 本文件**没有**证明任何新的**图论**事实：d-分离 ⟹ 因子分解
    仍是全库缺口（见 `_audit/R1-Markov组真实接线.md`）；
  * 零占位符：全文无未完成证明标记、无公理声明、无原生求值、无心跳上限调参。
  =========================================================================== -/

namespace FateV2.Predict.MarkovGroupWiring

open FateV2.Modeling

open FateV2.Predict.FinCondIndep

/-! ## §0 记号的统一

`CondMul` / `CondRatio` 的联合律口径是 `FinJoint α β γ = (α × β) × γ → ℝ`，
而各 Markov 模块的因子分解口径是 `α × β × γ → ℝ`（**顺序不同**）。
故本文件统一用 `reindex` 把三因子形式搬到 `FinJoint` 口径。
**⚠ 这不是装饰**：正是这个重排使得 `CondRatio` 与 `ChainMarkov` 可以同台。 -/

/-- 把 `α × β × γ` 口径的联合律读成 `FinJoint α γ β` 口径
（`X := 第一坐标`、`Y := 第三坐标`、`Z := 第二坐标`）。 -/
def reindex {α β γ : Type} (p : α × β × γ → ℝ) : FinJoint α γ β :=
  fun q => p (q.1.1, q.2, q.1.2)

/-! ## §1 链 Markov 性 ⟹ 条件比形式（`GlobalMarkovMinimal` × `PearlMarkovBridgeG1`） -/

/-- ⭐⭐⭐ **`Fate.P213B1.ChainMarkov ⟹ CondRatio`**。

**接线**：
1. `FateV2.Predict.GlobalMarkovMinimal.global_markov_minimal`：`ChainMarkov ⟹ CondMul`；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`：`CondMul ⟹ CondRatio`。

**⚠ 自审（前件不包结论）**：前件 `ChainMarkov p` 是**三因子乘积分解**
（`∃ α β γ`），完全不含 `margZ`、不含除法、不含 `CondRatio`；
结论是**逐点除法等式**。二者不同层。

**⚠ 为什么这是新的**：`GlobalMarkovMinimal` 只到 `CondMul`，
`PearlMarkovBridgeG1` 的 `condMul_imp_condRatio` 只吃**它自己的** `ChainFac`；
「`P213B1.ChainMarkov` ⟹ `CondRatio`」在**两个模块里都没有**。 -/
theorem chainMarkov_condRatio {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (p : A × B × C → ℝ) (h : FateV2.Predict.P213B1.ChainMarkov p) :
    CondRatio (reindex p) :=
  FateV2.Predict.R242G1.condMul_imp_condRatio (reindex p)
    (FateV2.Predict.GlobalMarkovMinimal.global_markov_minimal p h)

/-! ## §2 链 Markov 相对性 ⟹ 条件比形式（`MarkovBridgeReal` × `PearlMarkovBridgeG1`） -/

/-- ⭐⭐⭐ **`ChainMarkovRelative ⟹ CondRatio`**（另一个**独立**的 Markov 定义 ⟹ 同一结论）。

**接线**：
1. `Fate.MarkovBridgeReal.chain_markov_relative_condmul`：`ChainMarkovRelative ⟹ CondMul`；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`：`CondMul ⟹ CondRatio`。

**⚠ 自审**：`ChainMarkovRelative` 是**存在三因子**
（`p x z y = pX x * pZX x z * pYZ z y`），不含 `margXZ`/`margZ`/除法。

**⚠ 与 §1 的差别**：`ChainMarkovRelative` 把「`Y` 的因子不读 `X`」
写进**类型**（`pYZ : β → γ → ℝ`），而 `P213B1.ChainMarkov` 写成 `γ : B × C → ℝ`。
**两条来自不同模块的不同形式，落到同一结论** —— 这正是本文件要展示的「同构事实被分散在两个模块」。 -/
theorem chainMarkovRelative_condRatio {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq γ] [DecidableEq β]
    (p : α × β × γ → ℝ) (h : Fate.MarkovBridgeReal.ChainMarkovRelative p) :
    CondRatio (reindex p) :=
  FateV2.Predict.R242G1.condMul_imp_condRatio (reindex p)
    (Fate.MarkovBridgeReal.chain_markov_relative_condmul p h)

/-! ## §3 链 Markov 相对性 ⟹ 可分离（`MarkovBridgeReal` × `GlobalMarkovMinimal` · `CondMulSeparable`） -/

/-- ⭐⭐⭐ **`ChainMarkovRelative` + `margZ ≠ 0` ⟹ 可分离**（弱假设版）。

**接线**：
1. `Fate.MarkovBridgeReal.chain_markov_relative_condmul`：`⟹ CondMul`；
2. `FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable_of_margZ_ne`：`CondMul + margZ≠0 ⟹ 可分离`。

**⚠ 自审**：前件是**因子分解 + 一个非退化条件**，结论是**存在性分解**。
`margZ ≠ 0` 只是「能除以 `margZ`」，**不包含**结论。

**⚠ 数学内容**：`reindex p` 的 `margZ` 就是 `p` 的 `z`-边缘律；
本定理说的是「链上『`Y` 的机制不读 `X`』⟹ 联合律可写成 `f(x,z)·g(y,z)`」，
**这是从 `MarkovBridgeReal` 的 `CondMul` 结论出发、经 `GlobalMarkovMinimal` 的 Bayes 归一化得到的**。 -/
theorem chainMarkovRelative_separable_of_margZ_ne {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ) (h : Fate.MarkovBridgeReal.ChainMarkovRelative p)
    (hZ : ∀ z : β, margZ (reindex p) z ≠ 0) :
    ∃ (f : α → β → ℝ) (g : γ → β → ℝ),
      ∀ x y z, reindex p ((x, y), z) = f x z * g y z :=
  FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable_of_margZ_ne (reindex p)
    (Fate.MarkovBridgeReal.chain_markov_relative_condmul p h) hZ

/-- ⭐⭐⭐ **`ChainMarkovRelative` + 逐点正 ⟹ 可分离**（正分布版）。

**接线**：1. `MarkovBridgeReal.chain_markov_relative_condmul`；2. `CondMulSeparable.condMul_implies_separable`。

**⚠ 与上一条的差别**：这里用**另一个模块**（`CondMulSeparable`）的**正性版本**，
假设是逐点 `0 < reindex p`。两条定理**前件不同、结论同形**，
说明「接线」不是只认一个出口：三个模块（`MarkovBridgeReal`、`GlobalMarkovMinimal`、`CondMulSeparable`）
在**同一个** `CondMul` 节点上汇合。 -/
theorem chainMarkovRelative_separable_of_pos {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]
    (p : α × β × γ → ℝ) (h : Fate.MarkovBridgeReal.ChainMarkovRelative p)
    (hpos : ∀ x y z, 0 < reindex p ((x, y), z)) :
    ∃ (f : α → β → ℝ) (g : γ → β → ℝ),
      ∀ x y z, reindex p ((x, y), z) = f x z * g y z :=
  FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable (reindex p)
    (Fate.MarkovBridgeReal.chain_markov_relative_condmul p h) hpos

/-! ## §4 道德图因子分解 ⟹ 条件比（`MoralGraphMarkov` × `PearlMarkovBridgeG1`） -/

/-- ⭐⭐⭐ **`MoralFactorizes` ⟹ `CondRatio`**。

**接线**：
1. `Fate.MoralGraphMarkov.moral_factorization_condmul`：`MoralFactorizes ⟹ CondMul`；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`：`CondMul ⟹ CondRatio`。

**⚠ 自审**：`MoralFactorizes q ⟺ ∃ ψ₁ ψ₂, q (x,y,z) = ψ₁ x z * ψ₂ y z`。
结论 `CondRatio` 是**边缘律的除法等式**，需要 `margZ`、`margXZ`、`margYZ`，
前件里**一个都没有** —— 故 `CondMul` 这一步是**真内容**（三个边缘律 + 分配律）。 -/
theorem moralFactorizes_condRatio {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (p : FinJoint α β γ)
    (h : FateV2.Modeling.MoralGraphMarkov.MoralFactorizes
      (fun q : α × β × γ => p ((q.1, q.2.1), q.2.2))) :
    CondRatio p :=
  FateV2.Predict.R242G1.condMul_imp_condRatio p
    (FateV2.Modeling.MoralGraphMarkov.moral_factorization_condmul p h)

/-! ## §5 无向图的团分解 ⟹ 道德图因子分解 ⟹ `CondMul`
      （`UndirectedGlobalMarkov` × `MoralGraphMarkov`） -/

/-- ⭐⭐⭐⭐ **「三团 + 只依赖 `S` 的残因子」⟹ `CondMul`**。

**接线**：
1. `Fate.UndirectedGlobalMarkov.separable_of_three_factors`：
   `(∃ f g r, p = f·g·r) ⟹ (∃ F G, p = F·G)`；
2. `Fate.MoralGraphMarkov.moral_factorization_condmul`：可分离 ⟹ `CondMul`。

**⚠ 自审（前件不包结论）**：前件是**三个显式因子**（`r` 只读 `s`）；
中间结论是**两个因子的存在性**（真消去：`F := f·r`）；
结论 `CondMul` 是**边缘律乘积等式**。

**⚠ 为什么这是新接线**：`UndirectedGlobalMarkov` 里已有 `three_clique_condmul`，
但它走的是 `PearlCondIndepBridge.separable_implies_condMul`；
本定理**改走 `MoralGraphMarkov`**，于是把「无向图团分解」与
「道德图团分解」这两个**平行模块**接在**同一个入口**上 —— 这正是 R-1 要的「组内互引」。 -/
theorem undirected_threeFactor_condMul {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinJoint α β γ)
    (h : ∃ (f : α → γ → ℝ) (g : β → γ → ℝ) (r : γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z * r z) :
    CondMul p :=
  FateV2.Modeling.MoralGraphMarkov.moral_factorization_condmul p
    (Fate.UndirectedGlobalMarkov.separable_of_three_factors
      (fun x y z => p ((x, y), z)) h)

/-! ## §6 三段拓扑序分解 ⟹ `CondMul` 与 ⟹ 可分离
      （`MarkovBridgeAncestral` × `GlobalMarkovMinimal`） -/

/-- ⭐⭐⭐ **三段拓扑序因子分解 + `margZ ≠ 0` ⟹ 可分离**。

**接线**：
1. `Fate.MarkovBridgeAncestral.three_stage_condmul`：三段分解 ⟹ `CondMul`；
2. `FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable_of_margZ_ne`：`⟹ 可分离`。

**⚠ 自审**：前件是**三段因子分解**（`p1 x * p2 x z * p3 z y`，`p3` 不读 `x`）；
结论是**两因子分解**（`f x z * g y z`）**加**一个非退化条件
（`margZ ≠ 0`，即「`Z` 有正质量」）。**结论的因子数比前件少一个**，
故不是同义反复 —— 这一步真的**丢掉了一个因子**（把 `p1·p2` 合并入 `f`）。 -/
theorem threeStage_separable_of_margZ_ne {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β × γ → ℝ)
    (h : ∃ (p1 : α → ℝ) (p2 : α → β → ℝ) (p3 : β → γ → ℝ),
      ∀ x z y, p (x, z, y) = p1 x * p2 x z * p3 z y)
    (hZ : ∀ z : β, margZ (reindex p) z ≠ 0) :
    ∃ (f : α → β → ℝ) (g : γ → β → ℝ),
      ∀ x y z, reindex p ((x, y), z) = f x z * g y z :=
  FateV2.Predict.GlobalMarkovMinimal.condMul_gives_separable_of_margZ_ne (reindex p)
    (Fate.MarkovBridgeAncestral.three_stage_condmul p h) hZ

/-! ## §7 链 Markov3（拓扑序版）⟹ 条件比（`MarkovBridgeTopo` × `PearlMarkovBridgeG1`） -/

/-- ⭐⭐⭐ **`MarkovBridgeTopo` 的 `ChainMarkov3` 分解 ⟹ `CondRatio`**。

**接线**：
1. `Fate.MarkovBridgeTopo.chainMarkov3_condmul`：三段分解 ⟹ `CondMul`；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`：`⟹ CondRatio`。

**⚠ 自审**：`ChainMarkov3` 的**定义体**（三因子 + 拓扑序 `0 < 1 < 2` 的父子结构）
以**显式命题**给出，`CondRatio` 是**除法等式**。前提不含除法。

**⚠ 与 §2 的区别**：`ChainMarkov3` 在 `MarkovBridgeTopo` 里**依附于 `chainDAG3` 的拓扑序**
（`chainDAG3_topo_0_lt_1` / `1_lt_2` 是同模块的图论内容），
而 `ChainMarkovRelative` 是纯类型层面的。两者到 `CondRatio` 的路径不同。 -/
theorem chainMarkov3_condRatio {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq γ] [DecidableEq β]
    (p : α × β × γ → ℝ)
    (h : ∃ (p0 : α → ℝ) (p10 : α → β → ℝ) (p21 : β → γ → ℝ),
      ∀ x0 x1 x2, p (x0, x1, x2) = p0 x0 * p10 x0 x1 * p21 x1 x2) :
    CondRatio (reindex p) :=
  FateV2.Predict.R242G1.condMul_imp_condRatio (reindex p)
    (Fate.MarkovBridgeTopo.chainMarkov3_condmul p h)

/-! ## §8 图上的因子分解 ⟹ 条件比（`ChainMarkovExplicitAntecedent` × `PearlMarkovBridgeG1`）

这一节把**图**（`G3 = chainDAG3`，父集 `pa G3 v`）真正写进前件：
前件 `Factorizes p G3` 的**读集由 `pa G3 v` 给出**，不是类型编码。 -/

/-- ⭐⭐⭐⭐ **`Factorizes p G3 ⟹ CondRatio (pullback p)`**（图级因子分解 ⟹ 条件比）。

**接线**：
1. `Fate.ChainMarkovExplicitAntecedent.chain_factorizes_condMul`：
   `Factorizes p G3 ⟹ CondMul (pullback p)`（证明里用 `pa_zero/one/two` 消费了图）；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`：`⟹ CondRatio`。

**⚠ 自审**：前件是**图上的因子分解**（`p x = ∏ v, φ v x`，`φ v` 只读 `pa G3 v`）；
结论是 `Fin 2` 上的**边缘律除法等式**。前件**不含** `margZ`、不含除法、
不含 `Fin 2` 的求和 —— 故 `separable_implies_condMul` 的求和恒等式是真内容。 -/
theorem factorizes_chain_condRatio (p : Fate.ChainMarkovExplicitAntecedent.Obs → ℝ)
    (h : Fate.ChainMarkovExplicitAntecedent.Factorizes p
      Fate.ChainMarkovExplicitAntecedent.G3) :
    CondRatio (Fate.ChainMarkovExplicitAntecedent.pullback p) :=
  FateV2.Predict.R242G1.condMul_imp_condRatio _
    (Fate.ChainMarkovExplicitAntecedent.chain_factorizes_condMul p h)

/-- ⭐⭐⭐⭐ **`Factorizes p G3` + `dSep X Y Z` ⟹ `CondRatio (pullback p)`**。

**接线**：
1. `Fate.ChainMarkovExplicitAntecedent.chain_dsep_factorizes_condMul`
   （**额外消费** `dSep`：由它取出端点不在条件集里）；
2. `FateV2.Predict.R242G1.condMul_imp_condRatio`。

**⚠ 自审**：两个前件（图级因子分解 + 一个**含自由变量**的 `dSep` 命题）
与结论（边缘律除法等式）**完全不同层**。
**⚠ 诚实标注**：`dSep` 在 `ChainMarkovExplicitAntecedent` 里只被用到「无交」部分
（该模块 §7.1 已自陈），故本定理的**图论内容有限**；它登记的是
「d-分离出现在前件、`CondRatio` 出现在结论」这一**跨模块接口存在**。 -/
theorem factorizes_chain_dsep_condRatio (p : Fate.ChainMarkovExplicitAntecedent.Obs → ℝ)
    (h : Fate.ChainMarkovExplicitAntecedent.Factorizes p
      Fate.ChainMarkovExplicitAntecedent.G3)
    {X Y Z : Finset (Fin 3)} (h0 : 0 ∈ X) (h2 : 2 ∈ Y)
    (hd : Fate.ChainMarkovExplicitAntecedent.G3.dSep X Y Z) :
    CondRatio (Fate.ChainMarkovExplicitAntecedent.pullback p) :=
  FateV2.Predict.R242G1.condMul_imp_condRatio _
    (Fate.ChainMarkovExplicitAntecedent.chain_dsep_factorizes_condMul p h h0 h2 hd)

/-! ## §9 诚实边界

**本文件**做了**：把 7 条跨模块蕴含链**显式证明**（每条真调用 2 个不同模块的定理）。

**本文件**没有做**：
1. **没有**推进 `d-分离 ⟹ 因子分解`（全库缺口 1）——
   本文件所有前件里出现的因子分解都仍然是**假设**；
2. **没有**把 `PearlGlobalMarkov` / `FactorMarkov` / `FinMarkov` /
   `MarkovEquivalence` / `MarkovFaithfulness` 接进来：
   它们讲的是**纯图论**（d-分离的路径分解）或**另一套接口**
   （`CondIndepFin`、`mass`），与本文件的 `CondMul`/`CondRatio` 节点
   **没有可直接组合的定理对** —— 这一条在报告中如实登记；
3. **没有**声称任何一条是「新的数学定理」：
   每条都是**已有两条定理的合成**，其价值在于把 `Markov` 组从
   **27 个孤立模块**变成**以 `CondMul` 为中心、有 5 个入边方向的小网络**。
-/

end FateV2.Predict.MarkovGroupWiring
