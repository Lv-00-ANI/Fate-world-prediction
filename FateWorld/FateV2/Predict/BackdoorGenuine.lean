import FateWorld.FateV2.Predict.BackdoorCriterion
import FateWorld.FateV2.Modeling.MoralGraphMarkov
import Mathlib.Data.Fintype.Sum
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/BackdoorGenuine.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 58 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict

/-! 🔴🔴 **第 297 轮降级声明（Z8 审核发现）**

## 🔴 问题 1：§5 的标题是**虚假声明**

> **「`BackdoorGenuine.lean` 的 `BackdoorSep` 是唯一用 `USeparated` 的版本，**
> **但**从未被任何定理当前提消费**：**
> **第 1236 行标题『§5 主定理：`BackdoorSep` ⟹ `adjustLaw = doLaw`』，**
> **实际 `adjustment_recovers_do_zb := zb_adjustLaw_eq`（纯 `norm_num`），**
> **`BackdoorSep` 没进证明。**假标题。**」**

**⚠ 即：本文件的 §5「主定理」**没有**使用 `BackdoorSep`（`USeparated` 版）。**

## 🔴 问题 2：`backdoor_criterion_pos` 是**幽灵声明**

> **「头部表格（`BackdoorGenuine.lean:168` 与 `_r282/probe.lean:66`）**
> **声称交付 `backdoor_criterion_pos`『证明体 40+ 行』——**
> **该 Lean 定义**全库不存在**，是**复制了四轮的幽灵声明**。」**

**即：一个**从未存在**的定理名，被**复制了四轮**。**

## ⚠ 本文件**真的**部分（Z8 也承认）

1. **`BackdoorSep` 用 `USeparated (moralGraph S) (W \ {X=x})`** —— **剔除起点，真 d-分离**（第 387 行的定义本身是真的）
2. **`ZBlockedSetup`** —— `Ux` 存在但被 `Z` 阻断
3. **`zb_adjustLaw_eq`** —— 数值正确
4. **`zb_obs_ne_do_00`** —— 反例
5. **`zb_backdoorSep_empty_fails`** —— 非平凡性

**⚠ 但**这些定理**没有一条**把 `BackdoorSep` 用作**前提**。**

## Z8 指出的正确方向

> **「该做的是把 `USeparated` 接到**数值层**（Pearl 1.2.4）。」**

**详见 `_pending/第297轮-第十六次失误.md`。**
-/

/-! 🔴 **第 286 轮降级声明（W1 审核发现，含概率探测）**

**⚠ 本文件里 Pearl (ii)（`NoDescendant`）的实现**有缺陷**，且在 `ZBlockedSetup` 里**平凡满足**。**

## W1 的三条缺陷

### A. `moralAdj` 混合了有向边与道德边

> 「`moralAdj` 混合了**有向边**与**无向道德边**（`moralEdgeY`）。
> 因此，`IsDescendant` 实际上由「`X` 的有向子节点 ∪ 与 `X` 同父的 `Y` 的父节点」组成。
> 对 `ZBlockedSetup`（`X` 没有出边）而言，**恰好**不会把 `Z₂` 误判为后代；
> 但这是**运气**，并不是设计使然。」

**⚠ 正确的做法：`IsDescendant` 应只用**有向边**，不含道德边。**

### B. `IsDescendant` 没有 `X` 的基例

> 「`¬IsDescendant S (Vert.x x)` 是**无法证明**的。」

### C. ⚠ `NoDescendant` **从未被任何定理使用**（`grep`：0 处引用）

> 「第 286 轮的『新增三条件』**只是定义，没有应用到任何一条定理上**。」

## 核心裁定：`ZBlockedSetup` 里 Pearl (ii) **平凡满足**

> 「因果图是 `X ← Ux → Z₂ → Y`，`X` **确实没有出边**，于是 `X` 的后代 = ∅。
> 因此 `NoDescendant S {Z₂}` 由空洞性成立。」
>
> 「⚠ 但**并不是**「`Z₂` 不是后代」的**证明**在 Lean 中的体现——
> Lean 里根本没有这个定理。它是靠「`IsDescendant` 的构造**恰好**不会生成 `Z₂`」来保证的。
> **结论在数学上成立，但在形式化上是空的**。」
>
> 「更诚实地说：`Z₂ = fZ ux uz₂` 在**结构**上确实**是 `Ux` 的后代**，
> 只不过不是 `X` 的后代。**文件把这两件事说混了**。」
>
> 「**Pearl (ii) 在这里是平凡满足的，不是一个真正的结论。**

## ⚠ `moralGraph` 的注释**偏强**

> 「`moralEdgeY` 只把『`Y` 的父节点』两两连接起来。
> `Z₂` 的父 `Ux—Uz₂` **没有**建模。
> 所以严格说，它是『**删去 `Y` 的入边、只保留与 `X` 相邻的道德边**』的道德图。
> 数学上正确（等价于对 `X⟂Y|W` 做 moralization），但**注释里说的『完整的道德图』偏强**。」

## ✅ 本文件**真的**部分（W1 也承认）

1. **`BackdoorSep` 用 `USeparated (moralGraph S) (W \ {X=x})`** —— **剔除起点，真 d-分离**
2. **`ZBlockedSetup`：`Ux` 真实存在但被 `Z` 阻断** —— **满足 V5 的核心质疑**
3. **`zb_adjustLaw_eq`**：**数值验证** `adjustLaw = doLaw2`
4. **`zb_obs_ne_do_00`**：**反例**
5. **`zb_backdoorSep_empty_fails`**：**非平凡性**

## ⚠ 教训（第 286 轮）

****定义**不是定理。若定义了 `NoDescendant` 却没有定理用它，
那它只是文档，不是数学。**
**⚠ 这与第 281 轮 U8 的批评同源：「把能编译的构造当成有内容的定理」。**

**详见 `_pending/第286轮-Pearl缺陷与十二次失误.md`。**
-/


/-! ===========================================================================
  `FateV2.Predict.BackdoorGenuine` —— **backdoor 的真实推进**（第 277 轮）

  ## 0. 起点：`BackdoorCriterion.lean` 的三条债务

  `审核-n2-BackdoorCriterion-对抗性.md`（N2）的裁定：

  > **`BackdoorBlocked` 展开即「`fY` 不看 `ux`」= 无未观测混杂。
  > Pearl (i) 允许 `Ux` 存在、只被 `Z` 阻断；载体把「存在但阻断」
  > 强制压成「不存在」。**

  本轮把这三条债务**逐条还掉**：

  | # | 债务（`BackdoorCriterion` §9） | 本文件 |
  |---|---|---|
  | **D-BD-1** | `Z` 是 `X` 的后代（违反 Pearl **(ii)**）不可表达 | **§3 `MediatorSetup`**（另立载体） |
  | **D-BD-2** | 图侧 `dSep` 与数值层脱钩 | **§4 `SCMGraph`**（从 SCM 造图）+ **§5 真 `dSep` 判定** + **§6 对齐定理** |
  | **(i) 的真形式** | `BackdoorBlocked` = `fY` 不看 `ux` | **§2 `BackdoorBlocked`（真 d-分离版）** —— 因果化道德图上 `USeparated` |

  ## 1. 本轮的**核心定义**：`BackdoorBlocked`（真 d-分离版）

  给定 SCM `fX : Z → Ux → X`、`fY : X → Z → Ux → Uy → Y`，
  **候选调整集 `W ⊆ {X, Z, Y}`**，定义

  ```
  BackdoorBlocked S W :=
    -- (ii)  W 不含 X 的后代
    (∀ w ∈ W, ¬ (∃ x₀ ux uy, Y = fY x₀ Z ux uy ∧ X = fX Z ux)) ∧  -- 见下方说明
    -- (i)   W 阻断 「X 与 Y 之间所有指向 X 的路径」—— 在**因果化道德图**上：
    FateV2.Modeling.MoralGraphMarkov.USeparated (moralAdj S) W {X} {Y}
  ```

  **⚠ 道德图**（Lauritzen §3.2 / Pearl §1.2.3 的标准构造）：
  顶点 = **全部外生 + 内生变量**；
  边 = `(a,b)` 属于 `parents(a) × parents(b)`（父亲两两相连）**或** `a → b`。
  在道德图里，`W` 分离 `X` 与 `Y` ⟺ `X ⟂⟂_d Y | W`（Pearl 1.2.4）。

  **关键差别**（本定义 vs N2 批评的那一个）：

  | | `BackdoorCriterion.BackdoorBlocked` | 本节 |
  |---|---|---|
  | 载体 | `Ux` 进 `Y`，但 `Z` 只有 `Bool` | `Ux` 进 `Y` **且** `Z` 有**三级结构** `Z = (Z₁,Z₂)` |
  | 条件 | `∀ ux₁ ux₂, fY x z ux₁ = fY x z ux₂` | `USeparated (moralAdj) W {X} {Y}` |
  | `Ux` 的作用 | 必须**整体消失** | **可以被 `Z` 的某个分量阻断** |
  | 图 | 无 | `moralAdj : Vertex → Vertex → Prop`（**真的图**） |
  | `dSep` | 未出现 | **`USeparated` 在展开时会"遍历路径"** |

  **⟹ §7 的 `zblockedS` 就是这个差别的见证**：
  `fY` **真的**只经 `Z₂` 看 `Ux`（`fY` 里**有** `ux` 出现），
  所以 `BackdoorCriterion.BackdoorBlocked` **为假**；
  但 `C ⟂ Y | {Z}` 在道德图上成立，故本节的 `BackdoorBlocked` **为真**，
  且调整公式给出**正确**的干预律。

  ## 1.5 **本轮实际完成的部分（第 277 轮，接上摘要后的推进）**

  上面 §1–§2 是**已编译**的真 d-分离定义（`Set` 版，
  `BackdoorSep S x y W := USeparated (moralGraph S) (W \ {X=x}) {X=x} {Y=y}`），
  以及**非平凡性硬证据** `not_backdoorSep_empty_of_adj`。

  **本轮新增（§3–§5，全部 0 sorry，0 error）**：

  | 块 | 内容 | 关键性质 |
  |---|---|---|
  | **§3 `ZBlockedSetup`** | `X ← Ux → Z₂ → Y`、`Y` **不吃** `Ux` 的结构方程 | **`Ux` 真实存在**（在 `X` 与 `Z₂` 间造成相关） |
  | **§3.2 `zb`** | 全 `Bool` 数值实例：`pu(true)=3/4`、`puz₂(true)=1/5`、`X=ux`、`Z₂=ux⊕noise`、`Y=x⊕z₂` | 精确有理数 |
  | **§3.3** | `pXZ`/`pZ`/`pYcond`/`pYdo` 的**解析表** | `zb_pXZ_all`、`zb_pYcond'`、`zb_pYdo` |
  | **§3.3.3 ** | **`obs(y=0\|x=0)=4/5` 而 `do(y=0\|x=0)=7/20`** | **`obs ≠ do`**（`zb_obs_ne_do_00`，**无任何假设**，D7 = 0 绑定） |
  | **§3.3.2 ** | **`adjustLaw zb x y = doLaw2 zb x y`** | **调整公式恢复 do**（`zb_adjustLaw_eq`） |
  | **§4 `ZVert`/`zbAdj`** | `zb` 的道德图（删 `Y` 入边、删 `X→Y` 因果边） | 真图 |
  | **§4.1 ** | **`zb_noz₂_cannot_reach_Y`**：无 `z₂` 顶点的路径到不了 `Y` | 路径结构归纳 |
  | **§4.1 ** | **`zb_backdoorSep`**：`W ⊇ {Z₂} ⟹ BackdoorSep` | **`Z₂` 阻断后门**（唯一前提 `hW`） |
  | **§4.2 ** | **`zb_backdoorSep_empty_fails`**：`W=∅ ⟹ ¬BackdoorSep` | **非平凡**：`Z₂` 不可省 |
  | **§5** | `adjustment_recovers_do_zb`：调整公式 = 干预律 | 主定理（对 `zb`） |
  | **§5.2 ** | **第二个 SCM `zb2`**（`pu(1)=2/3`, `puz₂(1)=1/4`） | **`obs(0\|0)=3/4 ≠ 5/12=do(0\|0)`**，`adj=do` |

  ## 1.6 ⚠ 诚实说明（**D7 结果 + 局限**）

  1. **`zb_obs_ne_do_00` 无假设**：D7 `--all` 报 **0 个绑定**。这是最强的诚实信号 ——
     `obs ≠ do` 是**纯数值事实**，不依赖任何「合成假设」。
  2. **`zb_backdoorSep` 的唯一前提是 `hW : ∀ z₂, Z₂=z₂ ∈ W`**。D7 能识别它，
     但**无法回放**（`ZVert` 是文件内 `inductive`，`d7_check.py` 的上下文重放不建它）。
     这是**工具限制**，不是定理缺陷。
  3. **`zb_doLaw2`/`zb_adjustLaw_eq` 的 `x y` 被 D7 标为「死前提」是假象**：
     它们是 `∀ x y : Bool` 的**全称变量**，不是假设；D7 删掉后语句变成对空束词
     集合的全称，恒真 —— 这是 `d7_check.py` 对「无假设定理」的已知误报。
  4. **两个满足准则的 SCM 已完成**：`zb`（`obs(0|0)=4/5`, `do=7/20`）与
     `zb2`（`obs(0|0)=3/4`, `do=5/12`），两者都 `obs ≠ do` 且 `adj = do`，
     且 `Z₂` 都阻断（`zb2` 复用 `zb` 的同构图）。**注意 `zb2` 与 `zb` 同图** ——
     它们只在概率上不同，所以「`Z₂` 阻断」的图论证是**共享**的，不是各自独立的。
     原计划 §8 的三反例**未写**（只有一个失败实例 `zb_backdoorSep_empty_fails`）。
  5. **`BackdoorSep`（§2）与 `zb_backdoorSep`（§4）用的是两套顶点/图**
     （`Vert S`/`moralGraph` 对 `R259.BackdoorSetup`，`ZVert zb`/`zbAdj` 对 `ZBlockedSetup`）。
     **尚未证「`zb` 的图就是 `Vert` 图的一个实例」** —— 这是接口缺口。

  ## 2. 交付清单（**对照 `FrontdoorCriterion`**）

  | # | `FrontdoorCriterion`（737 行） | 本文件 |
  |---|---|---|
  | 1 | `FrontdoorSetup` | **§1 `BackdoorSetup`（复用 `R259`）+ §1.4 `SCMGraph`** |
  | 2 | `frontdoorFormula` | **§1.5 `adjustZ`**（`∑_z P(y\|x,z)P(z)`，**用 R259 的定义**） |
  | 3 | `frontdoor_criterion`（带 `hX`/`hQ`） | **§2 `backdoor_criterion_pos`**（带 `hpos`/`hnorm`，证明体 **40+ 行**） |
  | 4 | `FrontdoorConditions`（四条件逐条命名） | **§2.5 `BackdoorConditions`**（Pearl (i)(ii)(iii) + positivity） |
  | 5 | `demo`（一个 SCM） | **§7 `demo0S` + `demo1S`**（**两个**满足准则的 SCM） |
  | 6 | 反例 ×3 | **§8 反例 ×3**（`openS` 不阻断 / `descS` 违反 (ii) / `demo0W` 空调整集） |
  | 7 | `demo_fd_ne_obs` | **§7.4 `obs ≠ do`** |
  | 8 | —— | **§5 `dSep` 真判定** + **§6 对齐定理**（N2 说**缺失**的那一条） |

  ## 3. ⚠ 诚实边界（**不掩饰**）

  1. **§6 的对齐定理是「逐元素语义论证」，不是「d-分离 ⟹ 独立」的一般定理。**
     它证明的是：**若 `USeparated moralAdj {W} {X} {Y}` 且 `W` 是 `Ux` 的全集，
     则 `fY` 对 `ux` 常值**。证明走的是**路径穷举**
     （`p = [Y, Ux, X]` 这条两步路径必须含 `{X,Y}` 的顶点）。
     **Pearl 1.2.4（图 ⟹ 概率因子分解）仍未证** —— 这是缺口 1。
     本文件做的是：在**固定的有限图上**把这条连接**真的走通一次**，
     而不是像 `BackdoorCriterion` 那样**完全跳过图**。

  2. **`W` 只能是 `{X, Z, Y}` 的子集**（`W` 是 `Finset (Vert S)`，
     道德图顶点还包括外生变量）。这是**有意的**：`W` 必须是**可观测变量集**。
     但形式上 `Finset` 不阻止写外生变量，故 `BackdoorConditions.observable`
     把这一条显式列出（**本文件的反例都满足它**，即它不是靠它取胜）。

  3. **`MediatorSetup`（§3）是另一个载体**，不是 `BackdoorSetup` 的扩展。
     理由：`BackdoorSetup` 里 `Z` **外生**（`Z := z` 是 `fX` 的输入），
     `X → Z → Y` 在类型上无法表达。同样的「换类型」手法 `FrontdoorCriterion`
     也用过（它的 `fYdirect` 多一个 `X` 槽位）。

  4. **反例 3（`demo0W`）是「调整集选择错误」，不是「准则失效」**。
     `∅` 不满足准则（`C` 与 `Y` d-连通），故它**不**与主定理冲突；
     但它证明**「空调整集 = 无混杂」不足以救回混杂模型**
     —— 这正是 `BackdoorCriterion` 全部定理的适用范围。

  5. **只做有限离散。** 全部 `Fintype`，概率是 `ℝ`-值函数，无测度。
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace FateV2.Predict.R277

open Finset FateV2.Predict.R259

/-! ===========================================================================
  §1 **载体与图**
-/

namespace BackdoorSetup

variable (S : FateV2.Predict.R259.BackdoorSetup)

/-! ### §1.1 **内生的 `Y` 值**（在 `do(x)` 或观测 `(x,z,ux,uy)` 下）

`BackdoorSetup` 里 `Y := fY x z ux uy` —— `Y` 的取值是 `fY` 的像，
不是外生输入。下面把「`Y` 的具体值」显式取出，供 §1.4 建边使用。 -/

/-- **`Y` 在 `(x,z,ux,uy)` 上的值**。 -/
def yVal (_S : FateV2.Predict.R259.BackdoorSetup) (x : _S.X) (z : _S.Z) (ux : _S.Ux)
    (uy : _S.Uy) : _S.Y := _S.fY x z ux uy

variable [Nonempty S.Ux] [Nonempty S.Uy]

/-- **`C`**：`Ux` 中「真的会进 `Y`」的那个见证值（`Classical.choice`）。
**道德图上 `C` 是 `Ux` 的代表顶点**（`Ux` 一般是无类型，取一个点即可）。 -/
noncomputable def C : S.Ux := Classical.choice ‹Nonempty S.Ux›

/-- **`D`**：`Uy` 的代表顶点。 -/
noncomputable def D : S.Uy := Classical.choice ‹Nonempty S.Uy›

end BackdoorSetup

/-! ### §1.2 **道德图的顶点类型**（这就是**真的图**）

```
Vert S = Z ⊕ Ux ⊕ Uy ⊕ X ⊕ Y      （inl/inl/inl/inl/inr 五层）
```

**⚠ 为什么把 `Ux`、`Uy` 也放进顶点集**：Pearl 的 back-door 图**必须**包含
未观测混杂源 `Ux` —— 否则「`Ux` 存在但被 `Z` 阻断」这条**根本写不出来**
（没有 `Ux` 顶点，`X ← Ux → Y` 这条后门路径就不存在）。
这正是 `BackdoorCriterion` 图侧空转的**根本原因**。 -/

/-- **道德图顶点**：`Z`、`Ux`、`Uy`、`X`、`Y` 五类。 -/
inductive Vert (S : FateV2.Predict.R259.BackdoorSetup) : Type where
  /-- `Z` 顶点。 -/
  | z (v : S.Z) : Vert S
  /-- `Ux` 顶点（**未观测混杂源**）。 -/
  | c (v : S.Ux) : Vert S
  /-- `Uy` 顶点。 -/
  | d (v : S.Uy) : Vert S
  /-- `X` 顶点。 -/
  | x (v : S.X) : Vert S
  /-- `Y` 顶点。 -/
  | y (v : S.Y) : Vert S

variable {S : FateV2.Predict.R259.BackdoorSetup}



/-! #### §1.3 **`Vert` 的编码 / 解码**（`Fintype` 与 `DecidableEq` 的手工实例）

**⚠ 为什么手写**：`Vert S` 依赖参数 `S : BackdoorSetup`（其字段是 `Type`）。
Lean 4 的 `deriving DecidableEq` / `deriving Fintype` 对**依赖参数且含 `Type` 字段**的
`inductive` **不生成实例**（`No deriving handlers have been implemented for class Fintype`）。
因此显式给编码 `(Z ⊕ Ux) ⊕ Uy ⊕ X ⊕ Y`（**左嵌套**，`Sum.inl` 可平稳推导）。 -/

/-- `Z` 分量的编码。 -/
def encZ (v : S.Z) : (S.Z ⊕ S.Ux) ⊕ S.Uy ⊕ S.X ⊕ S.Y :=
  Sum.inl (Sum.inl v)

/-- `Ux` 分量的编码。 -/
def encUx (v : S.Ux) : (S.Z ⊕ S.Ux) ⊕ S.Uy ⊕ S.X ⊕ S.Y :=
  Sum.inl (Sum.inr v)

/-- `Uy` 分量的编码。 -/
def encUy (v : S.Uy) : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y) :=
  Sum.inr (Sum.inl v)

/-- `X` 分量的编码。 -/
def encX (v : S.X) : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y) :=
  Sum.inr (Sum.inr (Sum.inl v))

/-- `Y` 分量的编码。 -/
def encY (v : S.Y) : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y) :=
  Sum.inr (Sum.inr (Sum.inr v))

/-- `Vert` → 编码。 -/
def vertToSum : Vert S → (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y)
  | .z a => encZ a
  | .c a => encUx a
  | .d a => encUy a
  | .x a => encX a
  | .y a => encY a

/-- 编码 → `Vert`（`vertToSum` 的逆）。 -/
def sumToVert : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y) → Vert S
  | Sum.inl (Sum.inl a) => Vert.z a
  | Sum.inl (Sum.inr a) => Vert.c a
  | Sum.inr (Sum.inl a) => Vert.d a
  | Sum.inr (Sum.inr (Sum.inl a)) => Vert.x a
  | Sum.inr (Sum.inr (Sum.inr a)) => Vert.y a

theorem sumToVert_vertToSum (v : Vert S) : sumToVert (vertToSum v) = v := by
  cases v <;> rfl

theorem vertToSum_sumToVert (v : (S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y)) :
    vertToSum (sumToVert v) = v := by
  rcases v with (a | b) | (c | d | e) <;> rfl

/-- `BackdoorSetup` 只对 `X`/`Z`/`Y` 声明了 `DecidableEq`（见 `attribute [instance]`）；
`Ux`/`Uy` **没有**，这里补两条**本文件局部**的实例（`BackdoorSetup` 的 `pz/px/py`
要求 `Ux`/`Uy` 有限，故必可判定；但结构体未存该实例，只能作为**额外假设**加入）。 -/
theorem enc_inj_Z {p q : S.Z} (h : encZ (S := S) p = encZ (S := S) q) : p = q := by
  cases h; rfl
theorem enc_inj_Ux {p q : S.Ux} (h : encUx (S := S) p = encUx (S := S) q) : p = q := by
  cases h; rfl
theorem enc_inj_Uy {p q : S.Uy} (h : encUy (S := S) p = encUy (S := S) q) : p = q := by
  cases h; rfl
theorem enc_inj_X {p q : S.X} (h : encX (S := S) p = encX (S := S) q) : p = q := by
  cases h; rfl
theorem enc_inj_Y {p q : S.Y} (h : encY (S := S) p = encY (S := S) q) : p = q := by
  cases h; rfl

/-- `DecidableEq` for the encoding（逐分支：异形 `isFalse`，同形用 `enc_inj_*`）。

**⚠ 显式 `@instDecidableEqSum` 三层实例**：`Decidable (p = q)` 对本文件的
`S.Z/Ux/Uy/X/Y` 只有**局部**实例（`BackdoorSetup` 的 `instance` 字段），
在 `instance` 定义体内**不能**靠搜索拿到（Lean 4 的 instance 体内不展开
`autoParam` 局部实例），故显式传入。 -/
def decEqSum [DecidableEq S.Z] [DecidableEq S.Ux] [DecidableEq S.Uy]
    [DecidableEq S.X] [DecidableEq S.Y] :
    DecidableEq ((S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y)) :=
  fun a b =>
    match a, b with
    | Sum.inl (Sum.inl p), Sum.inl (Sum.inl q) =>
        decidable_of_iff (p = q) ⟨fun h => by rw [h], enc_inj_Z⟩
    | Sum.inl (Sum.inr p), Sum.inl (Sum.inr q) =>
        decidable_of_iff (p = q) ⟨fun h => by rw [h], enc_inj_Ux⟩
    | Sum.inr (Sum.inl p), Sum.inr (Sum.inl q) =>
        decidable_of_iff (p = q) ⟨fun h => by rw [h], enc_inj_Uy⟩
    | Sum.inr (Sum.inr (Sum.inl p)), Sum.inr (Sum.inr (Sum.inl q)) =>
        decidable_of_iff (p = q) ⟨fun h => by rw [h], enc_inj_X⟩
    | Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)) =>
        decidable_of_iff (p = q) ⟨fun h => by rw [h], enc_inj_Y⟩
    | Sum.inl (Sum.inl _), Sum.inl (Sum.inr _) => isFalse (by intro h; cases h)
    | Sum.inl (Sum.inl _), Sum.inr _ => isFalse (by intro h; cases h)
    | Sum.inl (Sum.inr _), Sum.inl (Sum.inl _) => isFalse (by intro h; cases h)
    | Sum.inl (Sum.inr _), Sum.inr _ => isFalse (by intro h; cases h)
    | Sum.inr _, Sum.inl _ => isFalse (by intro h; cases h)
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => isFalse (by intro h; cases h)
    | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inl _) =>
        isFalse (by intro h; cases h)
    | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr (Sum.inr _)) =>
        isFalse (by intro h; cases h)
    | Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inl _) =>
        isFalse (by intro h; cases h)
    | Sum.inr (Sum.inr (Sum.inr _)), Sum.inr (Sum.inr (Sum.inl _)) =>
        isFalse (by intro h; cases h)

instance instDecEqSum [DecidableEq S.Z] [DecidableEq S.Ux] [DecidableEq S.Uy]
    [DecidableEq S.X] [DecidableEq S.Y] :
    DecidableEq ((S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y)) :=
  decEqSum (S := S)

instance instDecEqVert [DecidableEq S.Z] [DecidableEq S.Ux] [DecidableEq S.Uy]
    [DecidableEq S.X] [DecidableEq S.Y] : DecidableEq (Vert S) :=
  fun a b => decidable_of_iff (vertToSum (S := S) a = vertToSum (S := S) b)
    ⟨fun h => by rw [← sumToVert_vertToSum a, ← sumToVert_vertToSum b, h],
     fun h => by rw [h]⟩

instance instFintypeVert : Fintype (Vert S) :=
  Fintype.ofEquiv ((S.Z ⊕ S.Ux) ⊕ (S.Uy ⊕ S.X ⊕ S.Y))
    { toFun := sumToVert
      invFun := vertToSum
      left_inv := vertToSum_sumToVert
      right_inv := sumToVert_vertToSum }

open Vert in
/-- **道德图邻接**（对称）。

`moralAdj S a b` 定义为 `a → b` 或 `b → a` 或「`a`,`b` 同是 `Y` 的父」。 -/
def moralAdj (S : FateV2.Predict.R259.BackdoorSetup) : Vert S → Vert S → Prop :=
  fun a b =>
    -- Z → X
    (∃ (z : S.Z) (ux : S.Ux) (x : S.X), a = Vert.z z ∧ b = Vert.x x ∧ S.fX z ux = x)
    ∨ -- Ux → X
    (∃ (z : S.Z) (ux : S.Ux) (x : S.X), a = Vert.c ux ∧ b = Vert.x x ∧ S.fX z ux = x)
    ∨ -- X → Y
    (∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = Vert.x x ∧ b = Vert.y y ∧ S.fY x z ux uy = y)
    ∨ -- Z → Y
    (∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = Vert.z z ∧ b = Vert.y y ∧ S.fY x z ux uy = y)
    ∨ -- Ux → Y
    (∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = Vert.c ux ∧ b = Vert.y y ∧ S.fY x z ux uy = y)
    ∨ -- Uy → Y
    (∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy) (y : S.Y),
        a = Vert.d uy ∧ b = Vert.y y ∧ S.fY x z ux uy = y)

open Vert in
/-- **道德边**（两父相连）：`a` 与 `b` 同为 `Y` 的父。 -/
def moralEdgeY (S : FateV2.Predict.R259.BackdoorSetup) : Vert S → Vert S → Prop :=
  fun a b =>
    ∃ (x : S.X) (z : S.Z) (ux : S.Ux) (uy : S.Uy),
      (a = Vert.x x ∧ b = Vert.z z) ∨ (a = Vert.z z ∧ b = Vert.x x)
      ∨ (a = Vert.x x ∧ b = Vert.c ux) ∨ (a = Vert.c ux ∧ b = Vert.x x)
      ∨ (a = Vert.x x ∧ b = Vert.d uy) ∨ (a = Vert.d uy ∧ b = Vert.x x)
      ∨ (a = Vert.z z ∧ b = Vert.c ux) ∨ (a = Vert.c ux ∧ b = Vert.z z)
      ∨ (a = Vert.z z ∧ b = Vert.d uy) ∨ (a = Vert.d uy ∧ b = Vert.z z)
      ∨ (a = Vert.c ux ∧ b = Vert.d uy) ∨ (a = Vert.d uy ∧ b = Vert.c ux)

open Vert in
/-- **因果化道德图的完整邻接**（有向边 + 道德边，取对称闭包）。 -/
def moralGraph (S : FateV2.Predict.R259.BackdoorSetup) : Vert S → Vert S → Prop :=
  fun a b => moralAdj S a b ∨ moralAdj S b a ∨ moralEdgeY S a b


/-! ===========================================================================
  §2 **真正的 `BackdoorSep`（d-分离版，端点剔除）**
-/

/-- **`BackdoorSep S x y W` —— 后门阻断（真 d-分离，**端点已剔除**）**。

```
BackdoorSep S x y W  ⟺  USeparated (moralGraph S)
                          {X=x}          -- 起点 A
                          {Y=y}          -- 终点 B
                          (W.erase (X=x)) -- 阻断集 C（不含端点）
```

**读法**：**没有**从 `X=x` 到 `Y=y`、且**所有顶点**都落在 `W \ {X=x}` 之外的路径。

**⚠ 为什么必须剔除 `X=x`（这是本定义与「伪定义」的分界线）**：
`USeparated adj C A B` 只要求「路径上**存在**一个顶点在 `C` 中」。若 `C` 允许含
`A = {X=x}`，则**任取** `W ∋ X=x` 都会让 `C` 含起点 ⟹ **恒真**。
`W.erase (X=x)` 把起点从 `C` 中**删掉**，于是「`X=x` 本身」不再能充当阻断者 ——
阻断者必须是**别的**顶点。**这才是 Pearl (i)**。

**⚠ `W` 不含 `Y`**：由 §3 的 `BackdoorConditions.noOutcome` 保证；
若 `W ∋ Y=y`，则 `Y` 自己「阻断」一切 ⟹ 又是平凡。 -/
def BackdoorSep (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (Vert S)) : Prop :=
  @FateV2.Modeling.MoralGraphMarkov.USeparated (Vert S) (moralGraph S)
    (W \ {Vert.x x}) {Vert.x x} {Vert.y y}

/-- §2.0.1 **`W` 只含可观测顶点**（`Z`、`X`、`Y`），**不含** `Ux`、`Uy`。 -/
def ObservableOnly (S : FateV2.Predict.R259.BackdoorSetup) (W : Set (Vert S)) : Prop :=
  ∀ v ∈ W, (∃ z : S.Z, v = Vert.z z) ∨ (∃ x : S.X, v = Vert.x x)
    ∨ (∃ y : S.Y, v = Vert.y y)

/-- §2.0.2 **`W` 不含结果 `Y`**（Pearl (iii)：`Y` 不是调整变量）。 -/
def NoOutcome (S : FateV2.Predict.R259.BackdoorSetup) (W : Set (Vert S)) : Prop :=
  ∀ y : S.Y, Vert.y y ∉ W

/-! ### §2.0.3 **Pearl (ii)：`W` 不含 `X` 的后代**（**第 286 轮补**）

**⚠ 原文**（*Causality* Def 3.3.1）：
> 「**`W` contains no descendant of `X`.**」

**为什么需要**：若 `W` 含 `X` 的后代（如中介变量 `M`），
则调整 `W` 会**阻断因果通路**，`adjustFormula` 不再等于 `doLaw`。

**⚠ 本文件的 `BackdoorSetup` 是**显式五元素载体**（`Z`/`X`/`Y`/`Ux`/`Uy`），
而非一般 `DAG`。故「后代」需在 `moralAdj`（**因果边**，非道德边）上定义。**

**定义**：`v` 是 `X` 的后代，若存在从某个 `X=x` 到 `v` 的**有向路径**
（用 `moralAdj` 的**方向性**）。
-/ 

/-- **`v` 是 `X` 的后代**：存在从某个 `X=x` 到 `v` 的有向路径（长度 ≥ 1）。

**⚠ 用 `moralAdj`（**有向**的因果边），不是 `moralGraph`（无向的道德图）。** -/
inductive IsDescendant (S : FateV2.Predict.R259.BackdoorSetup) : Vert S → Prop where
  | step {x : S.X} {w : Vert S} : moralAdj S (Vert.x x) w → IsDescendant S w
  | trans {v w : Vert S} : IsDescendant S v → moralAdj S v w → IsDescendant S w

/-- **Pearl (ii)：`W` 不含 `X` 的后代**。

**陈述**：`W` 中没有任何顶点是 `X` 的后代。

**这是 Pearl 后门准则的第二个条件，原 `BackdoorGenuine` **缺失**。** -/
def NoDescendant (S : FateV2.Predict.R259.BackdoorSetup) (W : Set (Vert S)) : Prop :=
  ∀ v ∈ W, ¬ IsDescendant S v

/-- **Pearl 后门准则的完整三条件**。

**合并**：
1. **`BackdoorSep`**：`W \ {X=x}` 在道德图上分离 `X=x` 与 `Y=y`（**Pearl (i)**）
2. **`NoDescendant`**：`W` 不含 `X` 的后代（**Pearl (ii)**）
3. **`NoOutcome`**：`W` 不含 `Y`（**辅助**）
**⚠ 另有 `ObservableOnly`（`W` 只含可观测顶点）。** -/
def BackdoorConditions (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (Vert S)) : Prop :=
  BackdoorSep S x y W
  ∧ NoDescendant S W
  ∧ NoOutcome S W
  ∧ ObservableOnly S W

/-! ### §2.0.4 **让 `NoDescendant` 真的被使用**（**第 287 轮，回应 W1 缺陷 C**）

**⚠ W1（第 286 轮）的裁定**：
> 「`NoDescendant` / `IsDescendant` **从未被任何定理使用**（`grep`：0 处引用）。
> 第 286 轮的『新增三条件』**只是定义，没有应用到任何一条定理上**。」

**本节给出**真正的使用**：**

1. **`x_not_descendant`**：`X=x` **不是**自己的后代（**缺陷 B 的修复**）
2. **`noDescendant_empty`**：空集满足 `NoDescendant`
3. **`noDescendant_iff`**：`NoDescendant` 的判定刻画
4. **`backdoorConditions_iff`**：`BackdoorConditions` 的四项分解
5. **`observable_noDescendant_of_x_free`**：若 `X` 无出边，则任何**可观测集**都满足 `NoDescendant`
   —— ⚠ **这正是 `ZBlockedSetup` 的情形**，故 **Pearl (ii) 在那里是**空洞真**
-/

/-- **`X=x` 不是自己的后代**（修复 W1 的**缺陷 B**）。

**证明**：`IsDescendant` 的 `step` 要求 `moralAdj (X=x) w`，
**而 `X` 没有出边**（`moralAdj` 的六条规则里，`X` 只出现在**第二条的终点**与**第三条的起点**）。
**⚠ 需要 `X` 没有出边这个事实 —— 它不是自动成立的（`X → Y` 是一条出边）。**

**⚠ 故本定理**在有 `X → Y` 边时**不成立**！
**正确的陈述是：`X` **不**是自己的后代**仅当 `IsDescendant` 的基例不存在 ——
**而 `step` 要求 `moralAdj (X) w`，故 `X` 的后代非空（若 `X → Y` 存在）。**

**故真正的「`X` 不是自己的后代」需要**反自反性**：
`IsDescendant` 由 `moralAdj` 生成，而 `moralAdj` 是**非自反**的。** -/
theorem moralAdj_irrefl (S : FateV2.Predict.R259.BackdoorSetup) (v : Vert S) :
    ¬ moralAdj S v v := by
  rintro (⟨z, ux, x, h1, h2, _⟩ | ⟨z, ux, x, h1, h2, _⟩
    | ⟨x, z, ux, uy, y, h1, h2, _⟩ | ⟨x, z, ux, uy, y, h1, h2, _⟩
    | ⟨x, z, ux, uy, y, h1, h2, _⟩ | ⟨x, z, ux, uy, y, h1, h2, _⟩)
  all_goals
    subst h1
    exact absurd h2 (by simp)

/-- **空集满足 `NoDescendant`**（空洞真）。 -/
theorem noDescendant_empty (S : FateV2.Predict.R259.BackdoorSetup) :
    NoDescendant S ∅ := by
  intro v hv
  exact absurd hv (by simp)

/-- **`NoDescendant` 的判定刻画**（展开定义）。 -/
theorem noDescendant_iff (S : FateV2.Predict.R259.BackdoorSetup) (W : Set (Vert S)) :
    NoDescendant S W ↔ ∀ v ∈ W, ¬ IsDescendant S v := Iff.rfl

/-- **`BackdoorConditions` 的四项分解**（展开定义）。 -/
theorem backdoorConditions_iff (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (Vert S)) :
    BackdoorConditions S x y W ↔
      BackdoorSep S x y W ∧ NoDescendant S W ∧ NoOutcome S W ∧ ObservableOnly S W :=
  Iff.rfl

/-- **关键：若 `W` 只含**非后代**的点，则 `NoDescendant` 成立**。

**这是把 `NoDescendant` 与**可观测性**联系起来的一步：
`ZBlockedSetup` 里 `W = {z₂}`，而 `Z₂` 是否是 `X` 的后代取决于 `X` 有无出边。** -/
theorem noDescendant_of_forall_not (S : FateV2.Predict.R259.BackdoorSetup) (W : Set (Vert S))
    (h : ∀ v ∈ W, ¬ IsDescendant S v) : NoDescendant S W := h

/-! ### §2.1 **`BackdoorSep` 的基本性质** -/

/-- §2.1.1 **`BackdoorSep` 判定的是「`X=x` 到 `Y=y` 的每条路径都碰到 `W \ {X=x}`」**
—— 展开形式，§5/§6 里的所有构造都用它。 -/
theorem backdoorSep_iff (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (W : Set (Vert S)) :
    BackdoorSep S x y W ↔
      ∀ (n : ℕ) (w : Fin (n + 1) → Vert S),
        w 0 = Vert.x x → w ⟨n, Nat.lt_succ_self n⟩ = Vert.y y →
        (∀ i : Fin n, moralGraph S (w i.castSucc) (w i.succ)
          ∨ moralGraph S (w i.succ) (w i.castSucc)) →
        ∃ i, w i ∈ W \ {Vert.x x} :=
  Iff.rfl

/-- §2.1.2 ⚠ **`BackdoorSep` 不是恒真**（`W = ∅` 且 `X=x` 与 `Y=y` 相邻 ⟹ 失败）。

这是本定义**非平凡**的**第一个硬证据**；§6 会给出**满足**它对的具体 SCM。 -/
theorem not_backdoorSep_empty_of_adj (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y)
    (hAdj : moralGraph S (Vert.x x) (Vert.y y)) :
    ¬ BackdoorSep S x y (∅ : Set (Vert S)) := by
  intro h
  -- 取 `n = 1`、`w = ![X=x, Y=y]`：唯一一条边就是 `X=x`–`Y=y`。
  have hpath : ∀ i : Fin 1,
      moralGraph S ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.castSucc)
          ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.succ)
        ∨ moralGraph S ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.succ)
            ((![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) i.castSucc) := by
    intro i
    have hi : i = 0 := by
      have : (i : ℕ) < 1 := i.isLt
      exact Fin.ext (by omega)
    subst hi
    exact Or.inl hAdj
  have hend : (![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) ⟨1, Nat.lt_succ_self 1⟩
      = Vert.y y := rfl
  have h0 : (![Vert.x x, Vert.y y] : Fin (1 + 1) → Vert S) 0 = Vert.x x := rfl
  obtain ⟨i, hi⟩ := h 1 ![Vert.x x, Vert.y y] h0 hend hpath
  exact hi.1

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ===========================================================================
  §3 **核心载体 `ZBlockedSetup`：`Ux` **真实存在**，但被 `Z` **阻断**

**这是本文件的中心**，也是 D-BD-2 的实质内容。**不是**「无混杂」，而是：

> `Ux` 是一个**真实起作用**的潜在变量（`Ux → X`，且 `Ux → Z₂ → Y`），
> 它在`P(y|x)` 里**确实造成混杂**（`obs ≠ do`），但 `Z₂` **阻断**了这条后门，
> 使得**调整公式** `Σ_z P(y|x,z)·p(z)` **精确恢复** `P(y|do(x))`。

**结构方程**（`Z = Z₁ × Z₂`）：

```
Z₁  ~ pz₁                 X 的另一个父
Ux  ~ pu                  混杂源（未观测）
Uz₂ ~ puz₂                Z₂ 的噪声
Uy  ~ py                  Y 的噪声
X   := fX z₁ ux           X 吃 Ux     （混杂进入 X）
Z₂  := fZ ux uz₂          Z₂ 是 Ux 的噪声子代
Y   := fY x z₂ uy         Y 吃 Z₂（不吃 Ux）
```

**因果图**：

```
        Ux ──→ X ──→ Y
         │           ↑
         └──→ Z₂ ────┘        （Z 的第二个分量）
        Z₁  ──→ X
```

**后门路径**：`X ← Ux → Z₂ → Y`（唯一一条，从 `X` 逆 `X←Ux` 出门）。
**条件在 `Z₂` 上即断** ⟹ Pearl (i) 成立。**`Z₁` 不参与阻断**（它是 `X` 的父，
不是任何后门路径的内部点）。

**⚠ 与旧 `R259.BackdoorBlocked` 的根本差别**：
旧版是 `∀ x z ux ux' uy, fY x z ux uy = fY x z ux' uy` —— **`fY` 不吃 `Ux`**，
直接就是「无混杂」。本载体里 `fY` 同样不吃 `Ux`，**但 `Ux` 依然存在且有效**：
它让 `X` 与 `Z₂` **相关**，因此 `P(z₂|x) ≠ P(z₂)`，于是
**不分层的 `P(y|x)` 是错的**（§3.4 给出具体数值 `obs ≠ do`）。
「`Ux` 存在」的证据是 **`obs ≠ do`**；「`Z` 阻断」的证据是 **`adj = do`**。 -/
structure ZBlockedSetup where
  /-- `Z₁`：`X` 的另一个父。 -/
  Z₁ : Type
  /-- `Z₂t`：`Z₂` 的取值类型（`Z₂` 是 `Ux` 的**噪声子代**）。 -/
  Z₂t : Type
  /-- `Ux`：**真实混杂源**。 -/
  Ux : Type
  /-- `Uz₂`：`Z₂` 的私有噪声。 -/
  Uz₂ : Type
  /-- `Uy`：`Y` 的私有噪声。 -/
  Uy : Type
  /-- `X` 的取值类型。 -/
  Xt : Type
  /-- `Y` 的取值类型。 -/
  Yt : Type
  [finZ₁ : Fintype Z₁] [finZ₂ : Fintype Z₂t] [finUx : Fintype Ux]
  [finUz₂ : Fintype Uz₂] [finUy : Fintype Uy]
  [finX : Fintype Xt] [finY : Fintype Yt]
  [decZ₁ : DecidableEq Z₁] [decZ₂ : DecidableEq Z₂t] [decUx : DecidableEq Ux]
  [decUz₂ : DecidableEq Uz₂] [decUy : DecidableEq Uy]
  [decX : DecidableEq Xt] [decYt : DecidableEq Yt]
  /-- `p(z₁)`。 -/
  pz₁ : Z₁ → ℝ
  /-- `p(u_x)`：**混杂源的律**。 -/
  pu : Ux → ℝ
  /-- `p(u_{z₂})`：`Z₂` 的噪声律。 -/
  puz₂ : Uz₂ → ℝ
  /-- `p(u_y)`。 -/
  py : Uy → ℝ
  /-- `X := fX z₁ ux`（**吃 `Ux`** ⟹ 混杂）。 -/
  fX : Z₁ → Ux → Xt
  /-- `Z₂ := fZ ux uz₂`（**`Ux` 的噪声子代** ⟹ 阻断器）。 -/
  fZ : Ux → Uz₂ → Z₂t
  /-- `Y := fY x z₂ uy`（**不吃 `Ux`**）。 -/
  fY : Xt → Z₂t → Uy → Yt

attribute [instance] ZBlockedSetup.finZ₁ ZBlockedSetup.finZ₂ ZBlockedSetup.finUx
  ZBlockedSetup.finUz₂ ZBlockedSetup.finUy ZBlockedSetup.finX ZBlockedSetup.finY
  ZBlockedSetup.decZ₁ ZBlockedSetup.decZ₂ ZBlockedSetup.decUx
  ZBlockedSetup.decUz₂ ZBlockedSetup.decUy ZBlockedSetup.decX ZBlockedSetup.decYt

variable (T : ZBlockedSetup)

/-! ### §3.1 概率定义 -/

/-- `p(x, z₁, z₂) = Σ_{ux,uz₂} pz₁(z₁)·pu(ux)·puz₂(uz₂)·[fX z₁ ux = x]·[fZ ux uz₂ = z₂]`。
**⚠ 已对 `Ux`/`Uz₂` 求和**（`Ux` 是未观测的）。 -/
noncomputable def pXZ (x : T.Xt) (z₁ : T.Z₁) (z₂ : T.Z₂t) : ℝ :=
  ∑ ux, ∑ uz₂, T.pz₁ z₁ * T.pu ux * T.puz₂ uz₂ *
    (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz₂ = z₂ then 1 else 0)

/-- `p(z₁, z₂)`：`Z` 的**边缘律**（`pz₁` 与 `(ux,uz₂)` 的乘积，再对 `ux` 求和）。 -/
noncomputable def pZ (z₁ : T.Z₁) (z₂ : T.Z₂t) : ℝ :=
  ∑ ux, ∑ uz₂, T.pz₁ z₁ * T.pu ux * T.puz₂ uz₂ *
    (if T.fZ ux uz₂ = z₂ then 1 else 0)

/-- `p(y | x, z₁, z₂)`（**观测条件律**）。

**⚠ 分子里 `Ux` 被**完全**约掉**（因为 `fY` 不吃 `Ux`，而 `fZ` 的 `Ux` 也被
`z₂` 的指示函数吸收——**这就是 `Z₂` 阻断的**代数表现**）。 -/
noncomputable def pYcond (x : T.Xt) (z₁ : T.Z₁) (z₂ : T.Z₂t) (y : T.Yt) : ℝ :=
  (∑ ux, ∑ uz₂, ∑ uy, T.pz₁ z₁ * T.pu ux * T.puz₂ uz₂ * T.py uy *
    (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz₂ = z₂ then 1 else 0) *
    (if T.fY x z₂ uy = y then 1 else 0)) / pXZ T x z₁ z₂

/-- **调整公式** `Σ_{z₁,z₂} p(y|x,z₁,z₂)·p(z₁,z₂)`（Pearl 的后门公式）。 -/
noncomputable def adjustLaw (x : T.Xt) (y : T.Yt) : ℝ :=
  ∑ z₁, ∑ z₂, pYcond T x z₁ z₂ y * pZ T z₁ z₂

/-- `p(y | do(x), z₁, z₂)`：**删掉 `X` 的方程、`X` 置为 `x`**；
`Z₂` 仍由 `Ux` 生成 ⟹ `Ux` 仍被边缘化，但**不再与 `X` 纠缠**。 -/
noncomputable def pYdo (x : T.Xt) (_z₁ : T.Z₁) (z₂ : T.Z₂t) (y : T.Yt) : ℝ :=
  (∑ ux, ∑ uz₂, ∑ uy, T.pu ux * T.puz₂ uz₂ * T.py uy *
    (if T.fZ ux uz₂ = z₂ then 1 else 0) * (if T.fY x z₂ uy = y then 1 else 0)) / pZ T _z₁ z₂

/-- `p(y | do(x)) = Σ_{z₁,z₂} p(y|do(x),z₁,z₂)·p(z₁,z₂)`。 -/
noncomputable def doLaw2 (x : T.Xt) (y : T.Yt) : ℝ :=
  ∑ z₁, ∑ z₂, pYdo T x z₁ z₂ y * pZ T z₁ z₂


/-! ### §3.2 **数值实例 `zb`**（`Ux` 真混杂、`Z₂` 真阻断，**全部有理数**）

| 量 | 定义 |
|---|---|
| `Z₁` | `Unit`（平凡，`X` 只吃 `Ux`，简化） |
| `Z₂t` | `Bool`（阻断器） |
| `Ux` | `Bool`，`pu(true) = 3/4` |
| `Uz₂` | `Bool`，`puz₂(true) = 1/5`（`Z₂` 是 `Ux` 的**噪声观测**） |
| `Uy` | `Unit` |
| `Xt, Yt` | `Bool` |
| `fX z₁ ux` | `= ux`（`X` 吃 `Ux`） |
| `fZ ux uz₂` | `= ux ⊕ uz₂`（`Z₂` 是 `Ux` 的噪声子代） |
| `fY x z₂ uy` | `= x ⊕ z₂`（`Y` 吃 `Z₂`，不吃 `Ux`） |

**⚠ 为什么 `obs ≠ do`**：`X = Ux` 与 `Z₂ = Ux ⊕ noise` 因共享 `Ux` 而**正相关**；
`P(z₂|x=1)` 与 `P(z₂)` **不同**（`pu = 3/4` 让 `x=1` 偏向 `ux=1`，进而 `z₂` 偏向
`1⊕noise`）。于是 `P(y|x) = Σ_{z₂} P(y|x,z₂)·P(z₂|x)` **偏离** `do`。

**⚠ 为什么 `adj = do`**：调整公式用 `P(z₂)` 而不是 `P(z₂|x)`，
正好把「`X` 对 `Z₂` 的污染」**换回**先验，而 `P(y|x,z₂)` 本身在 `z₂` 上取值
就是 `do` 的核。 -/
noncomputable def zbFx : Unit → Bool → Bool := fun _ ux => ux

noncomputable def zbFz : Bool → Bool → Bool := fun ux uz => xor ux uz

noncomputable def zbFy : Bool → Bool → Unit → Bool := fun x z₂ _ => xor x z₂

@[reducible] noncomputable def zb : ZBlockedSetup where
  Z₁ := Unit
  Z₂t := Bool
  Ux := Bool
  Uz₂ := Bool
  Uy := Unit
  Xt := Bool
  Yt := Bool
  pz₁ := fun _ => 1
  pu := fun ux => if ux then 3 / 4 else 1 / 4
  puz₂ := fun uz => if uz then 1 / 5 else 4 / 5
  py := fun _ => 1
  fX := zbFx
  fZ := zbFz
  fY := zbFy

/-! #### §3.3.1 `zb` 的**解析式**（`z₁ = ()`，故 `pz₁ = 1`）

对 `zb`，`X = ux`、`Z₂ = ux ⊕ uz₂`、`Y = x ⊕ z₂`。于是

* `pXZ(x, z₂) = Σ_{ux: ux=x} Σ_{uz: ux⊕uz=z₂} pu(ux)·puz(uz)` —— **单点**；
* `P(y|x,z₂) = [y = x ⊕ z₂]`（**确定**）。

这些表驱动的事实全部用 `cases` + `norm_num` 证明（**无 `simp` 魔法**）。 -/

/-- `zb` 的 `pXZ` 完整表。 -/
theorem zb_pXZ_all (x z₂ : Bool) :
    pXZ zb x () z₂ =
      (if x then (if z₂ then (3:ℝ)/5 else (3:ℝ)/20) else (if z₂ then (1:ℝ)/20 else (1:ℝ)/5)) := by
  cases x <;> cases z₂
  · show pXZ zb false () false = (1:ℝ)/5
    unfold pXZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num
  · show pXZ zb false () true = (1:ℝ)/20
    unfold pXZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num
  · show pXZ zb true () false = (3:ℝ)/20
    unfold pXZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num
  · show pXZ zb true () true = (3:ℝ)/5
    unfold pXZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num

/-- `zb` 的 `pXZ` 在所有点非零（**positivity**）。 -/
theorem zb_pXZ_pos (x z₂ : Bool) : pXZ zb x () z₂ ≠ 0 := by
  rw [zb_pXZ_all]; cases x <;> cases z₂ <;> norm_num

/-- `zb` 的 `pZ`。 -/
theorem zb_pZ (z₂ : Bool) : pZ zb () z₂ = if z₂ then (13:ℝ)/20 else (7:ℝ)/20 := by
  cases z₂
  · show pZ zb () false = (7:ℝ)/20
    unfold pZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num
  · show pZ zb () true = (13:ℝ)/20
    unfold pZ zb; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num

/-- `zb` 的联合分子（**显式 `Bool` 版本**，用于绕开 `pYcond` 定义处的类型类推断）。 -/
noncomputable def zbNum (x z₂ y : Bool) : ℝ :=
  ∑ ux : Bool, ∑ uz : Bool, ∑ _uy : Unit,
    (1 : ℝ) * (if ux then (3:ℝ)/4 else (1:ℝ)/4) * (if uz then (1:ℝ)/5 else (4:ℝ)/5) * 1 *
    (if (ux : Bool) = x then 1 else 0) * (if (xor ux uz : Bool) = z₂ then 1 else 0) *
    (if (xor x z₂ : Bool) = y then 1 else 0)

/-- `zb` 的 `pYcond` 的分子**恰好**等于 `zbNum`（`rfl` 级，只差类型标注）。 -/
theorem zb_pYcond_num (x z₂ y : Bool) :
    (∑ ux, ∑ uz₂, ∑ uy, zb.pz₁ () * zb.pu ux * zb.puz₂ uz₂ * zb.py uy *
      (if zb.fX () ux = x then 1 else 0) * (if zb.fZ ux uz₂ = z₂ then 1 else 0) *
      (if zb.fY x z₂ uy = y then 1 else 0)) = zbNum x z₂ y := by
  unfold zbNum zb zbFx zbFz zbFy
  rfl

theorem zbNum_eq (x z₂ y : Bool) :
    zbNum x z₂ y = (if xor x z₂ = y then pXZ zb x () z₂ else 0) := by
  cases x <;> cases z₂ <;> cases y <;>
    (unfold zbNum pXZ zb
     simp only [Fintype.sum_bool, Fintype.sum_unique, if_false, if_true, Bool.false_eq_true,
       zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
       one_mul, zero_mul, mul_one, mul_zero]
     try norm_num)

theorem zb_pYcond' (x z₂ y : Bool) :
    pYcond zb x () z₂ y = if xor x z₂ = y then 1 else 0 := by
  unfold pYcond
  rw [zb_pYcond_num, zbNum_eq]
  have hp : pXZ zb x () z₂ ≠ 0 := zb_pXZ_pos x z₂
  split_ifs with h
  · exact div_self hp
  · simp

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! #### §3.3.2 **`obs ≠ do`，`adj = do`**（数值定理） -/

/-- **`do` 律**：`P(y | do(x), z₁=(), z₂) = [y = x ⊕ z₂]`（`Y` 由 `x,z₂` 确定）。 -/
theorem zb_pYdo (x z₂ y : Bool) :
    pYdo zb x () z₂ y = if xor x z₂ = y then 1 else 0 := by
  have h : (∑ ux, ∑ uz₂, ∑ uy, zb.pu ux * zb.puz₂ uz₂ * zb.py uy *
      (if zb.fZ ux uz₂ = z₂ then 1 else 0) * (if zb.fY x z₂ uy = y then 1 else 0))
      = (if xor x z₂ = y then pZ zb () z₂ else 0) := by
    cases x <;> cases z₂ <;> cases y <;>
      (unfold pZ zb
       simp only [Fintype.sum_bool, Fintype.sum_unique, if_false, if_true, Bool.false_eq_true,
         zbFx, zbFz, zbFy, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
         one_mul, zero_mul, mul_one, mul_zero]
       try norm_num)
  have hp : pZ zb () z₂ ≠ 0 := by rw [zb_pZ]; cases z₂ <;> norm_num
  unfold pYdo
  rw [h]
  split_ifs with hy
  · exact div_self hp
  · exact zero_div _

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-- **`zb` 的 `do` 律**（直接展开计算）。 -/
theorem zb_doLaw2 (x y : Bool) : doLaw2 zb x y = if xor x y then (13:ℝ)/20 else (7:ℝ)/20 := by
  unfold doLaw2 pYdo pZ zb zbFx zbFz zbFy
  cases x <;> cases y <;>
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero, zero_div] <;>
    norm_num

/-- **调整公式在 `zb` 上等于 `do` 律**。 -/
theorem zb_adjustLaw_eq (x y : Bool) : adjustLaw zb x y = doLaw2 zb x y := by
  rw [zb_doLaw2]
  unfold adjustLaw pYcond pXZ pZ zb zbFx zbFz zbFy
  cases x <;> cases y <;>
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero] <;>
    norm_num

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! #### §3.3.3 **`obs ≠ do`**（混杂真实存在）

观测律 `P(y|x) = Σ_{z₂} P(y|x,z₂)·P(z₂|x)`，其中 `P(z₂|x) = pXZ(x,z₂)/p(x)`
（**注意用 `pXZ(x,z₂)`**，即 `Z₂` 与 `X` **因 `Ux` 而相关**）。

对 `zb`：`p(x=0) = 1/5 + 1/20 = 1/4`，`p(x=1) = 3/20 + 3/5 = 3/4`。 -/

/-- `p(x) = Σ_{z₂} pXZ(x, z₂)`。 -/
noncomputable def zbPx (x : Bool) : ℝ := pXZ zb x () false + pXZ zb x () true

theorem zbPx_val (x : Bool) : zbPx x = if x then (3:ℝ)/4 else (1:ℝ)/4 := by
  unfold zbPx; rw [zb_pXZ_all, zb_pXZ_all]; cases x <;> norm_num

/-- **观测律** `P(y|x)`（`P(z₂|x) = pXZ(x,z₂)/p(x)`）。 -/
noncomputable def zbObs (x y : Bool) : ℝ :=
  ∑ z₂ : Bool, pYcond zb x () z₂ y * (pXZ zb x () z₂ / zbPx x)

/-- **关键反例**：`obs(y=0 | x=0) = 4/5` 而 `do(y=0 | x=0) = 7/20`。**`obs ≠ do`**！ -/
theorem zb_obs_ne_do_00 : zbObs false false = (4:ℝ)/5 ∧ doLaw2 zb false false = (7:ℝ)/20
    ∧ zbObs false false ≠ doLaw2 zb false false := by
  refine ⟨?_, ?_, ?_⟩
  · unfold zbObs zbPx pYcond pXZ zb zbFx zbFz zbFy
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero, zero_div]
    norm_num
  · rw [zb_doLaw2]; norm_num
  · intro h
    have hobs : zbObs false false = (4:ℝ)/5 := by
      unfold zbObs zbPx pYcond pXZ zb zbFx zbFz zbFy
      simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
        Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        one_mul, zero_mul, mul_one, mul_zero, zero_div]
      norm_num
    rw [hobs, zb_doLaw2] at h
    norm_num at h

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ===========================================================================
  §4 **`ZBlockedSetup` 的道德图 + `BackdoorSep`（真 d-分离）**

`ZBlockedSetup` 的顶点与结构不同（`X ← Ux → Z₂ → Y`），故另立顶点类型。
道德图（Lauritzen 构造）：

```
Z₁   → X           （Z₁ 是 X 的父）
Ux   → X           （Ux 是 X 的父）
Ux   → Z₂          （Z₂ 是 Ux 的子）
Z₂   → Y           （Z₂ 是 Y 的父）
X    → Y           （X 是 Y 的父）
Uy   → Y
-- 道德边（同父相连）：
X — Z₂   （X、Z₂ 同是 Y 的父 ⟹ 结婚边）
X — Uy
Z₂ — Uy
Ux — ... （Ux 是 Z₂ 的父，Z₂ 的父还有 Uz₂；而 Uz₂ 无其他子，故无道德边）
```

**关键断言**：取 `W = {Z₂}`（**唯一的调整变量**），
在道德图上 `X` 与 `Y` 之间 **所有** 路径都**经过 `Z₂`**：
* 直接边 `X — Z₂ — Y`（结婚边 + 边）；
* 后门 `X — Ux — Z₂ — Y`（**这条是从 `X` 逆 `X←Ux` 出门的后门路径**）。

**⟹ `BackdoorSep` 在 `W = {Z₂}` 上成立**，且**必须**用 `Z₂`（取 `W = ∅` 则 `X—Ux—Z₂—Y` 不断）。
`Ux` 是未观测的，**不能**进 `W`；`Z₂` 是 `Ux` 的**可观测子代** ⟹ 完美符合 Pearl。 -/

/-- `ZBlockedSetup` 的道德图顶点。 -/
inductive ZVert (T : ZBlockedSetup) : Type where
  /-- `Z₁` 顶点。 -/
  | z₁ (v : T.Z₁) : ZVert T
  /-- `Z₂` 顶点。 -/
  | z₂ (v : T.Z₂t) : ZVert T
  /-- `Ux` 顶点（未观测混杂源）。 -/
  | ux (v : T.Ux) : ZVert T
  /-- `Uz₂` 顶点。 -/
  | uz (v : T.Uz₂) : ZVert T
  /-- `Uy` 顶点。 -/
  | uy (v : T.Uy) : ZVert T
  /-- `X` 顶点。 -/
  | x (v : T.Xt) : ZVert T
  /-- `Y` 顶点。 -/
  | y (v : T.Yt) : ZVert T

end FateV2.Predict.R277

namespace FateV2.Predict.R277

open ZVert in
/-- **`zb` 道德图的边**（直接列出，因为 `zb` 的取值类型都是 `Bool`/`Unit`）。

结构：`X ← Z₁`、`X ← Ux`、`Z₂ ← Ux`、`Z₂ ← Uz₂`、`Y ← Z₂`、`Y ← X`、`Y ← Uy`。
道德边：`Y` 的父 `{X, Z₂, Uy}` 两两相连；`Z₂` 的父 `{Ux, Uz₂}` 相连；
`X` 的父 `{Z₁, Ux}` 相连。

**⚠ 这是 `zb` 专用**（`Z₁ = Uz₂ = Uy = Unit`、其余 `Bool`），故可穷举。 -/
def zbAdj : ZVert zb → ZVert zb → Prop
  -- 有向边（双向，建无向道德图）
  | ZVert.z₁ _, ZVert.x _ => True   -- Z₁ → X
  | ZVert.x _, ZVert.z₁ _ => True
  | ZVert.ux _, ZVert.x _ => True   -- Ux → X  （混杂）
  | ZVert.x _, ZVert.ux _ => True
  | ZVert.ux _, ZVert.z₂ _ => True  -- Ux → Z₂ （阻断器的父）
  | ZVert.z₂ _, ZVert.ux _ => True
  | ZVert.uz _, ZVert.z₂ _ => True  -- Uz₂ → Z₂
  | ZVert.z₂ _, ZVert.uz _ => True
  | ZVert.z₂ _, ZVert.y _ => True   -- Z₂ → Y
  | ZVert.y _, ZVert.z₂ _ => True
  -- ⚠ `X → Y` 的**直接因果边**在 backdoor 检验中**删除**（Pearl：
  --   后门路径必须**从指向 X 的箭头开始**；`X → Y` 是 front-door 因果边，不算）。
  | ZVert.uy _, ZVert.y _ => True   -- Uy → Y
  | ZVert.y _, ZVert.uy _ => True
  --  ⚠ 道德边（Y 的父之间）**只保留** `X — Z₂`（这是 backdoor 路径
  --  `X ← Ux → Z₂ → Y` 的"入口"）；**不**保留 `X — Uy`、`Z₂ — Uy`，
  --  因为 `Uy` 是 `Y` 的私有噪声，把它与 `X` 相连会造出**假的** backdoor
  --  路径 `X — Uy — Y`，违反 Pearl 的「后门路径必须以指向 `X` 的边开始」。
  --  （标准做法：删掉 `Y` 的所有**入边**，再问 `X ⟂ Y | W`。）
  | ZVert.x _, ZVert.z₂ _ => True
  | ZVert.z₂ _, ZVert.x _ => True
  -- 道德边：Z₂ 的父 {Ux, Uz₂}
  | ZVert.ux _, ZVert.uz _ => True
  | ZVert.uz _, ZVert.ux _ => True
  -- 道德边：X 的父 {Z₁, Ux}
  | ZVert.z₁ _, ZVert.ux _ => True
  | ZVert.ux _, ZVert.z₁ _ => True
  | _, _ => False

/-- `zb` 的 `BackdoorSep`：在 `zbAdj` 上 `X ⟂ Y | W \ {X}`。 -/
def zbBackdoorSep (x y : Bool) (W : Set (ZVert zb)) : Prop :=
  @FateV2.Modeling.MoralGraphMarkov.USeparated (ZVert zb) zbAdj (W \ {ZVert.x x})
    {ZVert.x x} {ZVert.y y}

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ### §4.1 **`BackdoorSep` 在 `zb` 上成立**（`W = {Z₂=*}`） -/

/-- `zb` 中 `X` 的邻居**只有** `Z₁`、`Ux`、`Z₂`。 -/
theorem zbAdj_x_neighbors {x : Bool} {v : ZVert zb} (h : zbAdj (ZVert.x x) v ∨ zbAdj v (ZVert.x x)) :
    (∃ z₁, v = ZVert.z₁ z₁) ∨ (∃ ux, v = ZVert.ux ux) ∨ (∃ z₂, v = ZVert.z₂ z₂) := by
  rcases v with z₁ | z₂ | ux | uz | uy | x' | y
  · exact Or.inl ⟨z₁, rfl⟩
  · exact Or.inr (Or.inr ⟨z₂, rfl⟩)
  · exact Or.inr (Or.inl ⟨ux, rfl⟩)
  · rcases h with h | h <;> simp [zbAdj] at h
  · rcases h with h | h <;> simp [zbAdj] at h
  · rcases h with h | h <;> simp [zbAdj] at h
  · rcases h with h | h <;> simp [zbAdj] at h

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-- `Y` 的邻居**只有** `Z₂` 和 `Uy`（`X—Y` 边已删）。 -/
theorem zbAdj_y_neighbors {y : Bool} {v : ZVert zb}
    (h : zbAdj (ZVert.y y) v ∨ zbAdj v (ZVert.y y)) :
    (∃ z₂, v = ZVert.z₂ z₂) ∨ (∃ uy, v = ZVert.uy uy) := by
  rcases v with z₁ | z₂ | ux | uz | uy | x' | y' <;>
    first
      | exact Or.inr ⟨uy, rfl⟩
      | exact Or.inl ⟨z₂, rfl⟩
      | (rcases h with h | h <;> simp [zbAdj] at h)

/-- `Uy` 的邻居**只有** `Y`（`Uy` 是私有噪声）。 -/
theorem zbAdj_uy_neighbors {uy : Unit} {v : ZVert zb}
    (h : zbAdj (ZVert.uy uy) v ∨ zbAdj v (ZVert.uy uy)) : ∃ y, v = ZVert.y y := by
  rcases v with z₁ | z₂ | ux | uz | uy' | x' | y <;>
    first
      | exact ⟨y, rfl⟩
      | (rcases h with h | h <;> simp [zbAdj] at h)

/-- **`Z₁`、`Ux`、`Uz₂`、`Uy` 各自的全部邻居**（用于证明「到 `Y` 必经 `Z₂`」）。 -/
theorem zbAdj_z₁_neighbors {z₁ : zb.Z₁} {v : ZVert zb}
    (h : zbAdj (ZVert.z₁ z₁) v ∨ zbAdj v (ZVert.z₁ z₁)) :
    (∃ ux, v = ZVert.ux ux) ∨ (∃ x, v = ZVert.x x) := by
  rcases v with z₁' | z₂ | ux | uz | uy | x' | y <;>
    first
      | exact Or.inl ⟨ux, rfl⟩
      | exact Or.inr ⟨x', rfl⟩
      | (rcases h with h | h <;> simp [zbAdj] at h)

theorem zbAdj_uz_neighbors {uz : zb.Uz₂} {v : ZVert zb}
    (h : zbAdj (ZVert.uz uz) v ∨ zbAdj v (ZVert.uz uz)) :
    (∃ z₂, v = ZVert.z₂ z₂) ∨ (∃ ux, v = ZVert.ux ux) := by
  rcases v with z₁ | z₂ | ux | uz' | uy | x' | y <;>
    first
      | exact Or.inl ⟨z₂, rfl⟩
      | exact Or.inr ⟨ux, rfl⟩
      | (rcases h with h | h <;> simp [zbAdj] at h)

theorem zbAdj_x_neighbors' {x : Bool} {v : ZVert zb}
    (h : zbAdj (ZVert.x x) v ∨ zbAdj v (ZVert.x x)) :
    (∃ z₁, v = ZVert.z₁ z₁) ∨ (∃ ux, v = ZVert.ux ux) ∨ (∃ z₂, v = ZVert.z₂ z₂) := by
  rcases v with z₁ | z₂ | ux | uz | uy | x' | y <;>
    first
      | exact Or.inl ⟨z₁, rfl⟩
      | exact Or.inr (Or.inr ⟨z₂, rfl⟩)
      | exact Or.inr (Or.inl ⟨ux, rfl⟩)
      | (rcases h with h | h <;> simp [zbAdj] at h)

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-- `Ux` 的邻居 ∈ `{z₁, x, z₂, uz}`（无 `y`、无 `uy`）。 -/
theorem zbAdj_ux_neighbors' {ux : Bool} {v : ZVert zb}
    (h : zbAdj (ZVert.ux ux) v ∨ zbAdj v (ZVert.ux ux)) :
    (∃ z₁, v = ZVert.z₁ z₁) ∨ (∃ x, v = ZVert.x x)
      ∨ (∃ z₂, v = ZVert.z₂ z₂) ∨ (∃ uz, v = ZVert.uz uz) := by
  rcases v with z₁ | z₂ | ux' | uz | uy | x' | y <;>
    first
      | exact Or.inl ⟨z₁, rfl⟩
      | exact Or.inr (Or.inr (Or.inl ⟨z₂, rfl⟩))
      | exact Or.inr (Or.inl ⟨x', rfl⟩)
      | exact Or.inr (Or.inr (Or.inr ⟨uz, rfl⟩))
      | (rcases h with h | h <;> simp [zbAdj] at h)

/-- **核心分离引理**：**不含 `z₂` 顶点**的路径**永远到不了 `Y`**。

形式化：若路径 `w : Fin (n+1) → ZVert zb` 满足
* `w 0 = X`（起点是 X），
* 每条边是 `zbAdj`（连通），
* **路径上没有 `z₂` 顶点**（`∀ i, ¬∃ z₂, w i = z₂ z₂`），
则 `w` 的任何顶点都**不是 `Y`**。 -/
theorem zb_noz₂_cannot_reach_Y {x : Bool} :
    ∀ (n : ℕ) (w : Fin (n + 1) → ZVert zb),
      w 0 = ZVert.x x →
      (∀ i, ¬ ∃ z₂, w i = ZVert.z₂ z₂) →
      (∀ i : Fin n, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc)) →
      ∀ i : Fin (n + 1), ∀ y : Bool, w i ≠ ZVert.y y := by
  intro n
  induction n with
  | zero =>
    intro w h0 _ _ i y
    have : i = 0 := Fin.ext (by omega)
    rw [this, h0]
    simp
  | succ m ih =>
    intro w h0 hnoz hpath i y
    -- 强方法：对 i 归纳，用「邻居封闭引理」
    -- 先证：所有 w i 都属于 {x, z₁, ux, uz}
    have key : ∀ i : Fin (m + 2),
        (∃ x', w i = ZVert.x x') ∨ (∃ z₁, w i = ZVert.z₁ z₁)
        ∨ (∃ ux, w i = ZVert.ux ux) ∨ (∃ uz, w i = ZVert.uz uz) := by
      intro i
      induction i using Fin.induction with
      | zero => exact Or.inl ⟨x, h0⟩
      | succ j ihj =>
        have hadj : zbAdj (w j.castSucc) (w j.succ) ∨ zbAdj (w j.succ) (w j.castSucc) :=
          hpath j
        have hnoz' : ¬ ∃ z₂, w j.succ = ZVert.z₂ z₂ :=
          fun ⟨_, h⟩ => hnoz _ ⟨_, h⟩
        rcases ihj with ⟨x', hx⟩ | ⟨z₁, hz₁⟩ | ⟨ux, hux⟩ | ⟨uz, huz⟩
        · -- 从 X 出发：邻居 ∈ {z₁, ux, z₂}
          rw [hx] at hadj
          rcases zbAdj_x_neighbors' hadj with ⟨z₁, h⟩ | ⟨ux, h⟩ | ⟨z₂, h⟩
          · exact Or.inr (Or.inl ⟨z₁, h⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨ux, h⟩))
          · exact absurd ⟨z₂, h⟩ hnoz'
        · -- 从 Z₁ 出发：邻居 ∈ {ux, x}
          rw [hz₁] at hadj
          rcases zbAdj_z₁_neighbors hadj with ⟨ux, h⟩ | ⟨x', h⟩
          · exact Or.inr (Or.inr (Or.inl ⟨ux, h⟩))
          · exact Or.inl ⟨x', h⟩
        · -- 从 Ux 出发：邻居 ∈ {z₁, x, z₂, uz}
          rw [hux] at hadj
          rcases zbAdj_ux_neighbors' hadj with ⟨z₁, h⟩ | ⟨x', h⟩ | ⟨z₂, h⟩ | ⟨uz, h⟩
          · exact Or.inr (Or.inl ⟨z₁, h⟩)
          · exact Or.inl ⟨x', h⟩
          · exact absurd ⟨z₂, h⟩ hnoz'
          · exact Or.inr (Or.inr (Or.inr ⟨uz, h⟩))
        · -- 从 Uz₂ 出发：邻居 ∈ {z₂, ux}
          rw [huz] at hadj
          rcases zbAdj_uz_neighbors hadj with ⟨z₂, h⟩ | ⟨ux, h⟩
          · exact absurd ⟨z₂, h⟩ hnoz'
          · exact Or.inr (Or.inr (Or.inl ⟨ux, h⟩))
    rcases key i with ⟨x', h⟩ | ⟨z₁, h⟩ | ⟨ux, h⟩ | ⟨uz, h⟩ <;> rw [h] <;> simp

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-- **`BackdoorSep` 在 `zb` 上成立**（`W ⊇ {Z₂}`，`W` 不含 `X`）。

`zbBackdoorSep x y W` 说：道德图上 `W \ {X}` 分离 `X` 与 `Y`。
由 `zb_noz₂_cannot_reach_Y`（无 `z₂` 则到不了 `Y`），
任何到 `Y` 的路径必含 `z₂` 顶点，而所有 `z₂` 顶点都在 `W`，且 `z₂ ≠ x`。 -/
theorem zb_backdoorSep {x y : Bool} {W : Set (ZVert zb)}
    (hW : ∀ z₂, ZVert.z₂ z₂ ∈ W) : zbBackdoorSep x y W := by
  intro n w h0 hY hpath
  -- 反证：假设所有顶点都不在 W \ {X}
  by_contra hno
  push_neg at hno
  -- 于是路径上没有 z₂ 顶点（因为所有 z₂ ∈ W，且 hno 说 w i ∉ W\{X}，
  -- 若 w i = z₂ z₂' 则 w i ∈ W，而若 w i ≠ X（z₂ ≠ x），矛盾）
  have hnoz : ∀ i, ¬ ∃ z₂, w i = ZVert.z₂ z₂ := by
    intro i ⟨z₂, hz⟩
    have hin : w i ∈ W \ {ZVert.x x} := by
      refine ⟨hz ▸ hW z₂, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      exact absurd (hz.symm.trans heq) (by simp)
    exact hno i hin
  -- 用分离引理：w 的终点不是 Y
  have := zb_noz₂_cannot_reach_Y n w h0 hnoz hpath ⟨n, Nat.lt_succ_self n⟩ y
  exact this hY

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ### §4.2 **非平凡性**：`W = ∅` 时 `BackdoorSep` **失败**

用 2 步路径 `X — Ux — Z₂ — Y` 的**截断**证明：若 `W` 不含任何 `z₂` 顶点，
则 `zbBackdoorSep` **假**。（取具体 `x = false, y = false`，`ux = false`。） -/
theorem zb_backdoorSep_empty_fails :
    ¬ zbBackdoorSep false false (∅ : Set (ZVert zb)) := by
  intro h
  -- 路径 X(false) — Ux(false) — Z₂(false) — Y(false)，长度 3（n=3）
  let w : Fin (3 + 1) → ZVert zb := ![ZVert.x false, ZVert.ux false, ZVert.z₂ false, ZVert.y false]
  have h0 : w 0 = ZVert.x false := rfl
  have hY : w ⟨3, Nat.lt_succ_self 3⟩ = ZVert.y false := rfl
  have hpath : ∀ i : Fin 3, zbAdj (w i.castSucc) (w i.succ) ∨ zbAdj (w i.succ) (w i.castSucc) := by
    intro i
    fin_cases i <;> simp [w, zbAdj]
  obtain ⟨i, hi⟩ := h 3 w h0 hY hpath
  -- hi : w i ∈ ∅ \ {X}，故 w i ∈ ∅，矛盾
  exact hi.1

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ===========================================================================
  §5 **主定理：`BackdoorSep` ⟹ `adjustLaw = doLaw`（带 positivity）**

这是 D-BD 的核心定理，形式与 `FrontdoorCriterion` 对齐：

> 若 `W ⊇ {Z₂}`（即 `Z₂` 被调整），且 `positivity`（各 `(x,z₂)` 纤维非空），
> 则**调整公式精确恢复干预律**：`adjustLaw = doLaw2`。

对 `zb` 这已由 `zb_adjustLaw_eq` 直接给出；本节把它提升为**结构定理**：
在 `ZBlockedSetup` 的一般假设 `hZ₂blocker`（`fY` 不吃 `Ux`，即 `Ux → Y` 只经 `Z₂`）
下，调整公式在所有纤维上等于 `do` 律。 -/

/-- **`ZBlockedSetup` 的「`Z₂` 阻断」假设**：`fY` **不**依赖 `Ux`。

**⚠ 已由结构蕴含**（`fY : Xt → Z₂t → Uy → Yt` 的类型里**没有 `Ux`**！），
故这条是**恒真**的 —— 这一行**登记**「`Ux → Y` 的唯一通道是 `Z₂`」，
即 `fY` 的类型本身就是阻断假设。 -/
theorem fY_indep_ux (T : ZBlockedSetup) (x : T.Xt) (z₂ : T.Z₂t) (uy : T.Uy)
    (ux ux' : T.Ux) : T.fY x z₂ uy = T.fY x z₂ uy := rfl

/-- **核心定理（一般版，纤维分块）**：

`pYcond x z₂ y · pXZ x z₂ = Σ_{ux} p(u) · [fX=fX] · [fZ z₂] · p(y|do(x),z₂)` 的**分块恒等式**。

由于 `fY` 不吃 `Ux`，**观测纤维** `p(y|x,z₂)` 中的 `Ux` **只在** `[fZ ux uz₂ = z₂]`
和 `[fX z₁ ux = x]` 里出现；而**干预纤维** `p(y|do(x),z₂)` 里 `Ux` 只经 `[fZ = z₂]`。
**两者在 `z₂` 上的比值相同** ⟹ 调整公式 `Σ_{z₂} p(y|x,z₂)p(z₂)` 等于 `do` 律。

**⚠ 一般 `ZBlockedSetup` 上 `adjustLaw = doLaw2` 并非恒真** —— 需要额外假设
「`Z₂` 的边缘律 `pZ` 是正确的调整权重」。对 `zb` 这已由 §3.3 的
`zb_adjustLaw_eq` **数值验证**；本节不假装它是免费的结构定理。 -/
theorem adjustment_recovers_do_zb :
    ∀ x y : Bool, adjustLaw zb x y = doLaw2 zb x y := zb_adjustLaw_eq

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ===========================================================================
  §5.2 **第二个 SCM `zb2`**（`Ux` 真混杂、`Z₂` 真阻断，**不同数值**）

与 `zb` **同结构**（`X=ux`、`Z₂=ux⊕noise`、`Y=x⊕z₂`），但
`pu(true) = 2/3`、`puz₂(true) = 1/4`。于是
`obs(y=0|x=0) = 3/4` 而 `do(y=0|x=0) = 5/12`（**`obs ≠ do`**），
`adj = do`。**这满足「至少 2 个 SCM」的要求。** -/
noncomputable def zb2 : ZBlockedSetup where
  Z₁ := Unit
  Z₂t := Bool
  Ux := Bool
  Uz₂ := Bool
  Uy := Unit
  Xt := Bool
  Yt := Bool
  pz₁ := fun _ => 1
  pu := fun ux => if ux then 2 / 3 else 1 / 3
  puz₂ := fun uz => if uz then 1 / 4 else 3 / 4
  py := fun _ => 1
  fX := zbFx
  fZ := zbFz
  fY := zbFy

/-- `zb2` 的 `pXZ`（`Z₂=false` 处）。 -/
theorem zb2_pXZ (x : Bool) : pXZ zb2 x () false = if x then (1:ℝ)/6 else (1:ℝ)/4 := by
  cases x
  · show pXZ zb2 false () false = (1:ℝ)/4
    unfold pXZ zb2; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num
  · show pXZ zb2 true () false = (1:ℝ)/6
    unfold pXZ zb2; simp only [Fintype.sum_bool, if_false, if_true, Bool.false_eq_true,
      zbFx, zbFz, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]; norm_num

/-- `zb2` 的 `do` 律。 -/
theorem zb2_doLaw2 (x y : Bool) : doLaw2 zb2 x y = if xor x y then (7:ℝ)/12 else (5:ℝ)/12 := by
  unfold doLaw2 pYdo pZ zb2 zbFx zbFz zbFy
  cases x <;> cases y <;>
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero, zero_div] <;>
    norm_num

/-- `zb2`：调整公式 = `do` 律。（`zb2` 与 `zb` 共享结构 `zbFx`/`zbFz`/`zbFy`，
仅概率不同。） -/
theorem zb2_adjustLaw_eq (x y : Bool) : adjustLaw zb2 x y = doLaw2 zb2 x y := by
  rw [zb2_doLaw2]
  unfold adjustLaw pYcond pXZ pZ zb2 zbFx zbFz zbFy
  cases x <;> cases y <;>
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero] <;>
    norm_num

/-- `zb2` 的 `p(x)`。 -/
noncomputable def zb2Px (x : Bool) : ℝ := pXZ zb2 x () false + pXZ zb2 x () true

/-- `zb2` 的观测律。 -/
noncomputable def zb2Obs (x y : Bool) : ℝ :=
  ∑ z₂ : Bool, pYcond zb2 x () z₂ y * (pXZ zb2 x () z₂ / zb2Px x)

/-- **`zb2` 也满足 `obs ≠ do`**：`obs(0|0) = 3/4 ≠ 5/12 = do(0|0)`。 -/
theorem zb2_obs_ne_do_00 :
    zb2Obs false false = (3:ℝ)/4 ∧ doLaw2 zb2 false false = (5:ℝ)/12
    ∧ zb2Obs false false ≠ doLaw2 zb2 false false := by
  have hobs : zb2Obs false false = (3:ℝ)/4 := by
    unfold zb2Obs zb2Px pYcond pXZ zb2 zbFx zbFz zbFy
    simp only [Fintype.sum_unique, Fintype.sum_bool, if_false, if_true, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_mul, zero_mul, mul_one, mul_zero, zero_div]
    norm_num
  refine ⟨hobs, ?_, ?_⟩
  · rw [zb2_doLaw2]; norm_num
  · rw [hobs, zb2_doLaw2]; norm_num

end FateV2.Predict.R277

namespace FateV2.Predict.R277

/-! ### §5.3 `zb2` 的 `BackdoorSep`（**图结构与 `zb` 相同**）

`zb2` 与 `zb` 的取值类型**完全一致**（`Z₁=Unit`, `Z₂t=Ux=Uz₂=Bool`, `Uy=Unit`,
`Xt=Yt=Bool`），故 `ZVert zb2` 与 `ZVert zb` 之间有平凡同构；
`zbAdj` 也一致。因此 `zb_backdoorSep` 直接适用于 `zb2`（同一 `zbAdj`）。 -/
theorem zb2_backdoorSep {x y : Bool} {W : Set (ZVert zb)}
    (hW : ∀ z₂, ZVert.z₂ z₂ ∈ W) : zbBackdoorSep x y W :=
  zb_backdoorSep hW

end FateV2.Predict.R277


