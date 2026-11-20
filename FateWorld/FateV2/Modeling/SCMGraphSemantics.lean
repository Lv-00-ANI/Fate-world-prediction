import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Modeling.SCMGraph
import Mathlib.Tactic

/-!
  # Modeling · SCMGraphSemantics

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMGraphSemantics.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMSemantics, SCMGraph
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `FateV2.Modeling.SCMGraphSemantics` —— **把 `FateV2.Modeling.SCMGraph` 真正接进 `SCMSemantics`**
  ===========================================================================

  ## 0. 本文件解决的「假接线」问题

  `MM4` 任务要求「接线 `SCMGraph` → `SCMSemantics`（扇入 15）」。

  **核查发现（两种 grep 模式互校，见下）**：`Fate/FateV2.Modeling.SCMSemantics.lean` 第 2 行
  **早已**有 `import FateV2.Modeling.SCMGraph`，但全文**零处**引用 `SCMGraph` 的任何标识符
  （`SV` / `enc` / `dec` / `depUX` / `depXY` / `depUY` / `edge` / `SCMGraph`）。
  即：**import 挂了，但没有一个下游消费者。**

  ```
  grep -c "SCMGraph"          Fate/FateV2.Modeling.SCMSemantics.lean   →  1   （仅 import 行）
  grep -c "SV|enc|dec|edge"   Fate/FateV2.Modeling.SCMSemantics.lean   →  0
  ```

  **这种「只 import 不消费」在本项目历史上就是「假接线」**：`SCMGraph` 的 38 条定理
  仍然没有任何混凝土下游。本文件补上**真实消费** —— 不是再加一个空 import，
  而是**真的用 `SCMGraph` 的定理去证明 `SCMSemantics` 语境下的命题**。

  ## 1. 真正的语义缝隙在哪里

  | 侧 | 载体 | 定义位置 |
  |---|---|---|
  | **概率侧** | `jointLaw M : M.U × X × Y → ℝ`，`= pU u · [h_u x = y]` | `SCMSemantics` |
  | **图侧** | `edge M : SV M → SV M → Prop`（`SV M = U ⊕ (X ⊕ Y)`）| `FateV2.Modeling.SCMGraph` |

  两套语言**互不引用**：`jointLaw` 不知道图，`edge` 不知道概率。
  本文件建立**第一个真实的连接**：

  > ⭐ **`jointLaw` 在「实际事实点」`x = (sg u).1` 处非零 ⟹ 图侧存在边 `X → Y`。**

  这是**跨语言**的蕴含（概率测度的支集 ⇒ 有向图的边），前件与结论分属
  两个模块的不同定义，**不是同义反复**（纪律第 7 条自检见 §3）。

  ## 2. 内容清单

  | 定理 | 内容 | 消费的 `SCMGraph` 资产 |
  |---|---|---|
  | `card_SV` | `|SV M| = |U| + |X| + |Y|` | `SV.instFintype` 背后的 `Equiv`（`enc`/`dec`/`enc_dec`/`dec_enc`）|
  | `jointLaw_ne_zero_imp_edge_xy` | `jointLaw` 支集 ⇒ 图边 `X → Y` | `edge` 的定义 |
  | `jointLaw_support_edge_and_y_leaf` | 上一条 + `Y` 顶点是叶 | `edge`、`edge_from_y_false` |

  ## 3. 纪律第 7 条自检（前件是否包住结论）

  | 定理 | 前件 | 结论 | 是否重言 |
  |---|---|---|---|
  | `card_SV` | 无（仅 `M`） | 基数等式 | 否（需 `card_congr` + `card_sum` 真计算）|
  | `jointLaw_ne_zero_imp_edge_xy` | **概率侧** `jointLaw ≠ 0` | **图侧** `edge …` 存在 | 否（两套不同定义，跨语言蕴含）|
  | `jointLaw_support_edge_and_y_leaf` | 同左 | 图边 + `Y` 是叶（无出边）| 否 |

  **无 `sorry`、无 `axiom`、无 `admit`。**

  ## 4. 未做的部分（如实登记）

  * **反向**（图边 ⇒ `jointLaw ≠ 0`）**未证**：因为 `pU u` 可为零
    （`SCM` 结构无 `pU > 0` 约束），图边存在时 `jointLaw` 仍可能为 `0`。
    要证反向须先假定 `pU` 的支撑，本文件不引入额外假设。
  * **d-分离 ⇒ 条件独立**（真正的 Markov 桥）**未做** —— 本文件只做
    「概率支集 ⇒ 图边」这一步；`SCMSemantics` §68.4 已如实登记该大缺口。
  =========================================================================== -/

namespace FateV2.Modeling.SCMGraphSemantics

open FateV2.Modeling.SCMSemantics FateV2.Modeling.SCMGraph FateV2.Modeling.PearlHierarchy

universe u

variable {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ### §2.1 ⭐⭐ 顶点集 `SV M` 的基数

消费 `SV.instFintype` 背后的 `Equiv`（由 `enc`/`dec` 及双向互逆 `enc_dec`/`dec_enc`
构造）。证明需要 `Fintype.card_congr` 与 `Fintype.card_sum`，**不是定义展开**。 -/
theorem card_SV (M : FateV2.Modeling.PearlHierarchy.SCM X Y) :
    Fintype.card (SV M) = Fintype.card M.U + Fintype.card X + Fintype.card Y := by
  rw [Fintype.card_congr (Equiv.mk (SV.dec M) (SV.enc M) (SV.enc_dec M) (SV.dec_enc M)).symm]
  simp [Fintype.card_sum, Nat.add_assoc]

/-! ### §2.2 ⭐⭐⭐ 概率支集 ⇒ 图边（**跨语言桥**） -/

omit [Fintype X] [DecidableEq X] [Fintype Y] in
/-- ⭐⭐⭐ **`jointLaw` 在实际事实点非零 ⟹ 图侧有边 `X → Y`。**

**陈述**：若外生实现 `u` 使 `jointLaw (u, (X(u), v)) ≠ 0`（即概率质量真的落在
「`X = X(u)` 且 `Y = v`」），则图上存在边 `X(u) → v`。

**⚠ 为什么取 `x = (sg u).1`**：`jointLaw` 的定义**只看** `(sg u).2 x = y`
（不再筛 `(sg u).1 = x`），而 `edge (.x s) (.y v) := ∃ u, (sg u).1 = s ∧ (sg u).2 s = v`。
二者在 `s = (sg u).1` 处**恰好对齐** —— 这是本桥成立的**唯一**接口。

**⚠ 证明不需要 `pU u ≠ 0`**：`jointLaw = pU u · [条件]`，若 `pU u = 0` 则
`jointLaw = 0`，与非零前件矛盾，故前件已隐含指示子非零，反推 `(sg u).2 (sg u).1 = v`。 -/
theorem jointLaw_ne_zero_imp_edge_xy (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (u : M.U) (v : Y)
    (h : jointLaw M (u, ((M.sg u).1, v)) ≠ 0) :
    edge M (.x ((M.sg u).1)) (.y v) := by
  unfold FateV2.Modeling.SCMSemantics.jointLaw at h
  simp only at h
  have hind : (if (M.sg u).2 (M.sg u).1 = v then (1 : ℝ) else 0) ≠ 0 := by
    intro hz
    exact h (by rw [hz, mul_zero])
  have hyv : (M.sg u).2 (M.sg u).1 = v := by
    by_contra hne
    exact hind (if_neg hne)
  exact ⟨u, rfl, hyv⟩

/-! ### §2.3 ⭐⭐ 支集边 + `Y` 端是叶

同时消费 `SCMGraph.edge`（经上一条）与 `SCMGraph.edge_from_y_false`
（`Y` 是叶，无出边）。这条把「概率支集给出的边」与「图的层次结构」合起来。 -/
theorem jointLaw_support_edge_and_y_leaf (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (u : M.U) (v : Y)
    (h : jointLaw M (u, ((M.sg u).1, v)) ≠ 0) :
    edge M (.x ((M.sg u).1)) (.y v) ∧ ∀ b : SV M, ¬ edge M (.y v) b :=
  ⟨jointLaw_ne_zero_imp_edge_xy M u v h, edge_from_y_false M v⟩

end FateV2.Modeling.SCMGraphSemantics

/-! ===========================================================================
  §5  R-23：**S 系真接线** —— `SCMSemantics` / `SCMGraph` 的双向消费
  ===========================================================================

  ## 0. 本节解决什么（假接线审计）

  本模块原有的 3 条定理只消费**一条**接口：`jointLaw`（逐个体外生点）⟹ `edge`。
  其余两套语言**仍然互不相干**：

  * `SCMSemantics` 的 **`L1_obs` / `marginalX` / `condY` / `doLaw`**（已边缘化的
    `ℝ`-值总体律）—— 从未进入任何图侧陈述；
  * `SCMGraph` 的 **`depUX` / `depUY`**（图侧的依赖谓词）—— 从未决定任何
    语义侧的律等式。

  本节补两条**方向相反**的真接线：

  > ⭐ **语义 ⟹ 图**：`L1_obs (x, y) ≠ 0` ⟹ `edge (.x x) (.y y)`（§5.1）
  >
  > ⭐ **图 ⟹ 语义**：`¬ depUX M` ⟹ （在 `X` 的常值点处）`condY = doLaw`（§5.2）

  ## 1. 纪律第 7 条自检（前件是否已把结论包进去）

  | 定理 | 前件 | 结论 | 重言？ |
  |---|---|---|---|
  | `L1_obs_ne_zero_imp_edge_xy` | 概率侧 `L1_obs (x,y) ≠ 0`（一个**和**非零）| 图侧 `edge (.x x) (.y y)`（**存在**某个 `u` 的事实点对齐）| 否：需用「非零和 ⟹ 某项非零」反证，`edge` 是存在陈述，`L1_obs` 是和式 |
  | `L1_obs_ne_zero_imp_rank_lt` | 同上 | `rank (.x x) < rank (.y y)` | 否：前件不提 `rank`，结论由 `edge_rank_lt` 算出 |
  | `L1_obs_ne_zero_imp_y_leaf` | 同上 | `∀ b, ¬ edge (.y y) b` | 否：前件只谈一条边，结论是 `Y` 出度为 0 |
  | `exists_constX_of_not_depUX` | `¬ depUX M`（即 `¬¬∃ x₀, ∀u`）| `∃ x₀, ∀ u, (sg u).1 = x₀` | ⚠ **弱**：只差一步经典逻辑（见 §3 登记）|
  | `not_depUX_exists_condY_eq_doLaw` | 同上 | `∃ x₀, (∀u, ·) ∧ condY M x₀ = doLaw M x₀` | 否：**语义等式**那部分是实质的（消费 `condY_eq_doLaw_of_no_confound`）|
  | `marginalX_eq_zero_of_ne` | `x ≠ x₀`、`∀u, (sg u).1 = x₀` | `marginalX M x = 0` | 否：从图侧常值条件算出边缘律为 0 |
  | `doLaw_ne_zero_imp_exists` | 语义侧 `doLaw M x y ≠ 0` | `∃ u, (sg u).2 x = y`（逐个体响应）| 否：`doLaw` 是和式，结论是存在性 |

  ## 2. 诚实边界

  * **不做**跨模块新增 `import`：本模块头部的 import（`SCMSemantics`、`SCMGraph`）
    已**传递**提供本节全部上游（`PearlHierarchy`、`push`、`L1_obs`、`edge`、`rank`、
    `depUX`、`depUY`、`condY`、`doLaw`、`marginalX`）。故本节**零改动**既有行，
    `git diff --numstat` 的 `D = 0`。
    **代价**：`SCMUnificationA`、`SCMKernel` 等**未被本模块 import** 的
    S 系模块**无法**在此接线 —— 若要对它们接线，必须在文件头部加 `import`
    （会破坏 `D = 0`），故**本轮不做**，如实登记。
  * `not_depUX_exists_condY_eq_doLaw` 的**前件与「存在常值 `x₀`」只差一步经典逻辑**；
    真正的数学内容在 `condY M x₀ = doLaw M x₀`（筛选 `X = x₀` 的指示函数恒为 1，
    故观测律与干预律重合）。这一点在 §3 单独登记，不夸大为「深定理」。
  * 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide` / 零 `maxHeartbeats`。

  ## 3. 弱项的如实登记

  `SCMGraph.depUX M` 定义为 `¬ ∃ x₀, ∀ u, (sg u).1 = x₀`。因此 `¬ depUX M` 与
  `∃ x₀, ∀ u, (sg u).1 = x₀` 在**经典逻辑**下等价，`exists_constX_of_not_depUX`
  只是这条双重否定的消去 —— **它被登记为「接口定理」而非「新数学」**。
  它的价值是**下游可直接消费**（不必再重复 `by_contra`），并且它让
  `not_depUX_exists_condY_eq_doLaw` 的前件保持**图侧词汇**（`depUX`），
  从而完成「图 ⟹ 语义」的方向。
  ======================================================================== -/

namespace FateV2.Modeling.SCMGraphSemantics

open FateV2.Modeling.SCMSemantics FateV2.Modeling.SCMGraph FateV2.Modeling.PearlHierarchy

/-! ### §5.1 ⭐⭐⭐ **语义 ⟹ 图**：观测律支集给出图边 -/

/-- ⭐⭐⭐ **`L1_obs` 在 `(x, y)` 处非零 ⟹ 图上存在边 `X(x) → Y(y)`。**

**⚠ 与 §2.2 的 `jointLaw_ne_zero_imp_edge_xy` 的区别**（这是本节的主要新内容）：

| | 前件 | 口径 |
|---|---|---|
| §2.2 | `jointLaw M (u, ((sg u).1, v)) ≠ 0` | **逐个体**（外生点，`u` 固定）|
| 本节 | `M.L1_obs (x, y) ≠ 0` | **总体**（已对 `u` 边缘化：`∑_u pU u · [事实点 = (x,y)]`）|

边缘化后仍能取回图边，靠的是「**非零和 ⟹ 某项非零**」：
若无边，则对**每个** `u` 都有 `¬((sg u).1 = x ∧ (sg u).2 x = y)`，
被加项恒为 `0`，和为 `0`，矛盾。**不需要 `pU > 0`**（`pU` 为负也无妨，
因为被加项是 `0` 而非「正」）。

**⟹ 这是一条从「总体概率层」到「图结构层」的蕴含**，两端的定义分属
`SCMSemantics` 与 `SCMGraph`，前件**不含**任何 `edge` 信息。 -/
theorem L1_obs_ne_zero_imp_edge_xy {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y)
    (h : M.L1_obs (x, y) ≠ 0) :
    SCMGraph.edge M (.x x) (.y y) := by
  by_contra hc
  apply h
  rw [FateV2.Modeling.PearlHierarchy.SCM.L1_obs, push]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hkey : ((M.sg u).1, (M.sg u).2 (M.sg u).1) = (x, y)
  · exfalso
    obtain ⟨h1, h2⟩ := Prod.mk.inj hkey
    exact hc ⟨u, h1, by rw [← h1]; exact h2⟩
  · rw [if_neg hkey, mul_zero]

/-- ⭐⭐ **支集边的层次后果**：`rank (.x x) = 1 < 2 = rank (.y y)`。

消费 `SCMGraph.edge_rank_lt`（势函数 `U ↦ 0, X ↦ 1, Y ↦ 2`）。
前件**不含**任何 `rank` 信息，故不是重言。 -/
theorem L1_obs_ne_zero_imp_rank_lt {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y)
    (h : M.L1_obs (x, y) ≠ 0) :
    SCMGraph.rank (M := M) (.x x) < SCMGraph.rank (M := M) (.y y) :=
  SCMGraph.edge_rank_lt (L1_obs_ne_zero_imp_edge_xy M x y h)

/-- ⭐⭐ **支集边 + `Y` 端出度为 0**：消费 `SCMGraph.edge_from_y_false`。

这两条合起来说明「`L1_obs` 的支集只落在 `X → Y` 这一层，`Y` 是叶」——
**是 §2.3 的总体律版本**。 -/
theorem L1_obs_ne_zero_imp_y_leaf {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y)
    (h : M.L1_obs (x, y) ≠ 0) :
    SCMGraph.edge M (.x x) (.y y) ∧ ∀ b : SCMGraph.SV M, ¬ SCMGraph.edge M (.y y) b :=
  ⟨L1_obs_ne_zero_imp_edge_xy M x y h, SCMGraph.edge_from_y_false M y⟩

/-! ### §5.2 ⭐⭐⭐ **图 ⟹ 语义**：`¬ depUX` 迫使观测律 = 干预律 -/

/-- ⭐ **`¬ depUX M` ⟹ 存在 `X` 的常值 `x₀`**（双重否定消去）。

**登记为接口定理**：`depUX M` 的定义就是 `¬ ∃ x₀, ∀ u, (sg u).1 = x₀`，
故本定理只做经典逻辑消去。它的作用是让下游**用图侧词汇**陈述结论。

**⚠ 诚实标注**：这**不是**新数学，见文件 §3。 -/
theorem exists_constX_of_not_depUX {X Y : Type} (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (h : ¬ SCMGraph.depUX M) : ∃ x₀ : X, ∀ u : M.U, (M.sg u).1 = x₀ := by
  by_contra hc
  exact h (by simpa [SCMGraph.depUX] using hc)

/-- ⭐⭐⭐ **`X` 不随外生 `U` 变 ⟹ 观测律 = 干预律**（**backdoor 的最简特例**）。

**图侧前件**：`¬ depUX M`（图上没有实质的 `U → X` 依赖）。
**语义侧结论**：存在 `x₀` 使 `condY M x₀ = doLaw M x₀` —— 即「筛选 `X = x₀`」
与「替换 `X := x₀`」给出**同一条** `Y` 的律。

**⟹ 为什么这是真接线**：前件是 `SCMGraph` 的图谓词，结论是 `SCMSemantics`
的两条律的等式；中间需要 `condY_eq_doLaw_of_no_confound` 的证明（把
`[sg u .1 = x₀]` 因子用 `hconst` 化为 `1`，再逐项消去）。**前件不含任何律等式。**

**⚠ 边界**：结论里的 `x₀` 是**图侧常值点**，不是任意 `x`。对 `x ≠ x₀`，
`condY M x = 0`（见 `marginalX_eq_zero_of_ne` 的同款论证），故等式不成立 ——
这是**如实的**最强形式。 -/
theorem not_depUX_exists_condY_eq_doLaw {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (h : ¬ SCMGraph.depUX M) :
    ∃ x₀ : X, (∀ u : M.U, (M.sg u).1 = x₀) ∧
      FateV2.Modeling.SCMSemantics.condY M x₀ = FateV2.Modeling.SCMSemantics.doLaw M x₀ := by
  obtain ⟨x₀, hx₀⟩ := exists_constX_of_not_depUX M h
  exact ⟨x₀, hx₀, FateV2.Modeling.SCMSemantics.condY_eq_doLaw_of_no_confound M x₀ hx₀ rfl⟩

/-- ⭐⭐ **常值 `X` 下，其它点的边缘律严格为 `0`。**

消费 `FateV2.Modeling.SCMSemantics.marginalX` 的定义与图侧常值条件：`x ≠ x₀` 时
`[sg u .1 = x]` 对**每个** `u` 恒为假。

**⟹ 这是 `not_depUX_exists_condY_eq_doLaw` 边界登记的形式化**
（「等式只在 `x₀` 处成立」的原因）。 -/
theorem marginalX_eq_zero_of_ne {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y)
    (x₀ : X) (hx₀ : ∀ u : M.U, (M.sg u).1 = x₀) {x : X} (hx : x ≠ x₀) :
    FateV2.Modeling.SCMSemantics.marginalX M x = 0 := by
  unfold FateV2.Modeling.SCMSemantics.marginalX
  apply Finset.sum_eq_zero
  intro u _
  rw [hx₀ u, if_neg (Ne.symm hx), mul_zero]

/-- ⭐⭐ **干预律的支撑 ⟹ 逐个体响应存在**：`doLaw M x y ≠ 0` 给出
**某个体** `u` 使 `(sg u).2 x = y`。

**⟹ 这是一条「总体 `ℝ`-律 ⟹ 个体机制」的蕴含**（与 §5.1 的
「总体 ⟹ 图」平行）：`doLaw` 是 `∑_u pU u · [h_u x = y]`，和为 `0` 之外
必有被加项非零。**不需要 `pU > 0`**。 -/
theorem doLaw_ne_zero_imp_exists {X Y : Type} [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y] (M : FateV2.Modeling.PearlHierarchy.SCM X Y) (x : X) (y : Y)
    (h : FateV2.Modeling.SCMSemantics.doLaw M x y ≠ 0) : ∃ u : M.U, (M.sg u).2 x = y := by
  by_contra hc
  push Not at hc
  apply h
  unfold FateV2.Modeling.SCMSemantics.doLaw
  apply Finset.sum_eq_zero
  intro u _
  rw [if_neg (hc u), mul_zero]

end FateV2.Modeling.SCMGraphSemantics
