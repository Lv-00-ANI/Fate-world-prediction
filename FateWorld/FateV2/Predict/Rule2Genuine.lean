import FateWorld.FateV2.Predict.Rule23Semantic
import FateWorld.FateV2.Predict.DoCalculusRules
import FateWorld.FateV2.Predict.CausalDirection
import FateWorld.FateV2.Predict.GraphOps
import FateWorld.FateV2.Predict.CausalPath
import FateWorld.FateV2.Predict.CausalDescendant
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.EquivFin
import FateWorld.FateV2.Predict.InterventionSup
/-!
  # Predict · Rule2Genuine

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Rule2Genuine.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Rule23Semantic, DoCalculusRules, CausalDirection, GraphOps, CausalPath, CausalDescendant, InterventionSup
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/Rule2Genuine` —— **缺口 3：规则 2 的真语义版本**
  （第 248 轮）

  ## ⚠⚠ 一、本文件要修的是哪一条

  **第 247 轮 J1 的审核结论**（见 `Fate/Rule23Semantic.lean` 文件头）：

  | 定理 | 证明体 | 判定 |
  |---|---|---|
  | `R246G3.rule2_semantic` | `fun x z y => h x z y` | ❌ **前提就是结论**（P3 级）|
  | `R246G3.rule3_semantic` | `fun x z y => h x z y` | ❌ 同上 |
  | `R242G3.rule1_no_confounding` | `fun x y => h x y` | ❌ 同上 |

  **根因**：`Rule2Condition M` 的**定义**逐字就是 `∀ x z y, doLaw2 = doLawXCond`，
  故「前提 ⟹ 结论」只是**定义展开**，**零内容**。

  **本文件的做法**：**不删不改** `Rule23Semantic.lean`，**另建一层**，
  前提换成**真正关于结构（方程的依赖集）的条件**。

  ## ⭐⭐⭐ 二、新旧定义对照（**核心交付**）

  ### 旧定义（**问题所在**，`Fate/Rule23Semantic.lean` §6）

  ```lean
  /-- ⭐⭐ **规则 2 的前提**（**⚠ 这是被 J1 判定为 P3 的那一条**）。 -/
  def Rule2Condition (M : Sem3.SCM3 Z X Y) [DecidableEq Z] [DecidableEq Y] : Prop :=
    ∀ (x : X) (z : Z) (y : Y), Sem3.doLaw2 M x z y = Sem3.doLawXCond M x z y
  ```

  **⟹ 前提 ≡ 结论。**`rule2_semantic` 的证明体 `fun x z y => h x z y` 只是**搬运**。

  ### 新定义（**本文件**，§2）

  ```lean
  /-- ⭐⭐⭐⭐ **中介不变量**：`Y` 的方程 `f_u(z,x)` **不读 `x`**。
      即 `Y` 的方程**只依赖 `Z`（与自己的外生 `u`）** —— 任务书那句话的精确形式。 -/
  def MediationInvariant (M : R246G3.Sem3.SCM3 Z X Y) : Prop :=
    ∀ (u : M.U) (p₁ p₂ : Z × X), p₁.1 = p₂.1 → (M.sg u).2 p₁ = (M.sg u).2 p₂
  ```

  **⭐⭐ 形态对照**：

  | | 旧 `Rule2Condition` | 新 `MediationInvariant` |
  |---|---|---|
  | **论域** | `X × Z × Y`（**取值空间**）| `M.U × (Z×X) × (Z×X)`（**外生 × 方程参数**）|
  | **内容** | 「两条定律相等」 | 「**方程的值**在第一分量相同时**相同**」|
  | **与结论同形？** | ❌ **逐字相同** | ✅ **完全不同的命题** |
  | **可证伪** | ❌（恒真蕴含）| ✅ `conf` **满足** `MediationInvariant` 却仍**不满足**规则 2（`conf_invariant` + `conf_rule2_fails`）——⚠ 原文写的 `conf_not_invariant` **此名不存在，第 258 轮更正** |
  | **可实例化** | — | ✅ `chain` 满足（`chain_invariant`）|

  ## ⭐⭐⭐⭐⭐ 三、新定理（**本文件全部结果**）

  | # | 定理 | 类型 | 内容 |
  |---|---|---|---|
  | 1 | `medChainAdj_acyclic` / `medChainG` | [理论] | `X → Z → Y` 是**真 DAG**（沿秩严格增 ⟹ 无环）|
  | 2 | `medChainG_is_mediator` / `directG_not_mediator` | [理论] | 图条件**非恒真**（`X→Y` 时失败）|
  | 3 | `exists_medFactor_of_invariant` | [理论] | `MediationInvariant` ⟹ `∃ g, f_u(z,x) = g_u(z)` |
  | 4 | ⭐⭐⭐⭐ `zMass_eq_one` | [理论] | 归一化 + `Z` 为根 ⟹ `zMass M z = 1` |
  | 5 | ⭐⭐⭐⭐⭐ `doLaw2_eq_doLawX_of_invariant` | [理论] | **`MediationInvariant` ⟹ `doLaw2 = doLawX`**（**真 `Finset` 求和**）|
  | 6 | ⭐⭐⭐⭐⭐ `rule2_genuine` | **[理论] 主交付** | ⭐ **`P(y\|do(x),do(z)) = P(y\|do(x),z)`** |
  | 7 | ⭐⭐⭐⭐⭐ `chain_doLawXCond` / `chain_satisfies_rule2_genuine` | [验证] | 主结论在 `chain` 上**跑通**，闭式 `[z=y]` |
  | 8 | ⭐⭐⭐⭐⭐ `doLaw2_sub_doLawX` | **[理论] 核心恒等式** | ⭐ **两律之差 = `∑ pU·[zOf≠z]·[f_u=y]`**（**最有用**）|
  | 8b | ⭐⭐⭐⭐⭐ `doLaw2_eq_doLawX_iff` | **[理论] 充要条件** | ⭐ **规则 2 ⟺ 该和为零**（**最完整的回答**）|
  | 8c | ⭐⭐⭐⭐ `mediationInvariant_iff` | [理论] | `∀ z x x'` 等价形式（**展开级**，无新数学）|
  | 8d | ⭐⭐⭐⭐ `zIsRoot_forces_subsingleton` | **[理论] 载体局限** | ⚠ `ZIsRoot` ⟹ `Z` 单点（`rule2_genuine` 的适用面受限的**根因**）|
  | 9 | ⭐⭐⭐⭐⭐ `medChain_dsep_rule2` | **[理论] 图侧真定理** | ⭐ **规则 2 的 d-分离前提在纯中介图上**成立** |
  | 10 | ⭐⭐⭐⭐ `rule2Graph_medChain_no_Z_Y` / `rule2Graph_medChain_X_Z`（原文写的 `rule2Graph_medChain_facts` ⚠ 此名不存在，第 258 轮更正）| [验证] | `rule2Graph` 保留 `X → Z`、**删除** `Z → Y` |
  | 11 | ⭐⭐⭐⭐⭐ `chain_not_zIsRoot` | **[验证] 诚实边界** | ⚠ `chain` **不**满足 `ZIsRoot` ⟹ 主定理的**适用面被载体限制** |
  | 12 | ⭐⭐⭐⭐ `chain_zMass` / `conf_zMass` | [验证] | `zMass` 的真值（`1/2`），**非 1** |
  | 13 | ⭐⭐⭐⭐ `conf_invariant` | [验证] | `conf` **满足** `MediationInvariant` 却**不满足**规则 2 |

  ## ⚠⚠ 四、诚实的边界（**本章最重要，必须读**）

  ### 4.1 ① 图侧：d-分离前提**确实成立**（**好消息，且修正了我早先的误判**）

  在 Pearl 的 `G_{\underline X \overline Z}` 上：

  - `delOut G setZ` 删**「出点 ∈ `setZ`」的边** ⟹ **`Z → Y` 被删**；
  - `delIn _ setX` 删**「入点 ∈ `setX`」的边** ⟹ `X → Z` 的入点 `Z ∉ setX`，**保留**；
  - **净效果：图上只剩 `X → Z`，`Y` 是**孤立点**。**

  **⟹ `Z \perp\!\!\!\perp_d Y \mid X` **成立**（`medChain_dsep_rule2`，机器验证）。
  **⚠ 我在本轮**一度**把 `delIn`/`delOut` 的参数顺序记反，得出「前提不成立」的**错误结论**，
  **核查定义后已更正** —— 本文件登记这次更正，以免后人重蹈。**

  ### 4.2 ② 结构侧：主定理的真前提是「`Y` 的方程不读 `x`」

  **d-分离成立** ⟹ 按 Pearl 的论证，规则 2 应成立。
  **但本项目**还**没有「d-分离 ⟹ 条件独立」的桥（缺口 1）**，
  **故本文件**绕开 d-分离**，直接在**方程层**证：

  $$\textbf{MediationInvariant}(M) \wedge \textstyle\sum_u p_U(u) = 1
    \wedge \textbf{ZIsRoot}(M) \implies \mathrm{doLaw2} = \mathrm{doLawXCond}$$

  **这是**结构 ⟹ 定律**的真证明（§4 的 `Finset.sum_congr` + 换项 + 归一化），
  **且前提与结论**不同形**。** 两条路（图侧 / 结构侧）**互补**：
  **图侧给「应该成立」的直觉，结构侧给「为什么成立」的证明。**

  ### 4.3 ③ **载体**的固有局限（**这是本文件的**技术核心**，**必须读**）

  载体 `Sem3.SCM3 Z X Y = PearlHierarchy.SCM (Z × X) Y` 把 `Z` 的观测值**绑在外生上**
  （`zOf(sg u)`，**不依赖 `x`** 但**依赖 `u`**）。

  **⟹ `ZIsRoot`（要求 `zOf` 对**所有** `z` 恒定）在本载体上**几乎总是假的**：
  `chain` 违反它（`chain_not_zIsRoot`），`conf` 也违反（`conf_not_zIsRoot`）。
  **`ZIsRoot` 的唯一模型是 `Z` 为单点集。**

  **⟹ 主定理 `rule2_genuine` 的**证明是真的，但它的适用面在本载体上极窄**。
  **这不是定理的毛病，是载体的毛病**：`Z` 的取值**编码在外生里**，
  **故 `Z` 在本载体中**结构上不可能是 `X` 的真后代**。

  **⭐⭐ 具体后果（**必须记下**）**：`chain` 上规则 2 **确实成立**，
  **但不是**因为 `rule2_genuine`（`chain` 不满足 `ZIsRoot`）——
  **而是巧合**：`Y = z` 且 `Z = X = u`，使 `doLawX` 的筛选因子与 `[f_u = y]` **同步**。
  **`chain_satisfies_rule2_genuine` 用**直接计算**（`chain_doLawXCond`）证明它。

  ### 4.4 ④ 归一化守卫 `Supplied` **不可去**

  `zMass M z = 0` 时 `P(y\mid do(x),z) = doLawX/zMass` **无定义**（分母为零），
  **故它是**语义必要条件**，不是技术性回避。**

  ### 4.5 ⑤ `conf` 的教科书价值

  `conf` **满足** `MediationInvariant`（方程 `fun _ => u` 连 `p` 都不读）
  **却**不满足规则 2（`doLaw2 = 1/2` 而 `doLawXCond = [z=y]`）。
  **⭐⭐ 这精确地说明**：「`Y` 不读 `x`」**不足以**推出规则 2 ——
  **还需要「`Z` 的纤维质量在 `do(x)` 前后守恒」（`ZIsRoot`/`zMass = 1`）。**

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial` / `native_decide`。**

  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace R248

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1 ⭐⭐ **图侧**：三个具体 DAG
  =========================================================================== -/

/-- ⭐⭐ **三变量顶点** `{X, Z, Y}`（构造子名即语义）。 -/
inductive XZY where
  /-- 处理变量。 -/
  | vX
  /-- 中介变量。 -/
  | vZ
  /-- 结果变量。 -/
  | vY
  deriving DecidableEq

/-- ⭐ **`XZY` 的 `Fintype` 实例**（本文件的 `deriving` 链不提供它，故手写）。 -/
instance : Fintype XZY := Fintype.ofEquiv (Fin 3) (Equiv.mk
  (fun
    | 0 => XZY.vX
    | 1 => XZY.vZ
    | _ => XZY.vY)
  (fun
    | XZY.vX => 0
    | XZY.vZ => 1
    | XZY.vY => 2)
  (by intro a; fin_cases a <;> rfl)
  (by intro a; cases a <;> rfl))

/-- ⭐ **`{X}`**。 -/
def setX : Set XZY := fun v => v = XZY.vX

/-- ⭐ **`{Z}`**。 -/
def setZ : Set XZY := fun v => v = XZY.vZ

/-- ⭐ **顶点上的秩函数**（沿边严格增 ⟹ 任何路径严格增 ⟹ 无环）。 -/
def rk : XZY → ℕ
  | .vX => 0
  | .vZ => 1
  | .vY => 2

/-! ### §1.1 ⭐⭐ **纯中介图** `X → Z → Y` -/

/-- ⭐⭐⭐ **纯中介图的邻接**：**恰有 `X → Z` 与 `Z → Y` 两条边**。

**⚠ 关键：没有 `X → Y`。** -/
def medChainAdj : XZY → XZY → Prop
  | .vX, .vZ => True
  | .vZ, .vY => True
  | _, _ => False

/-- ⭐⭐ **`medChainAdj` 沿边严格增秩**。 -/
theorem medChainAdj_rk {a b : XZY} (h : medChainAdj a b) : rk a < rk b := by
  match a, b, h with
  | .vX, .vZ, _ => exact (by decide : rk XZY.vX < rk XZY.vZ)
  | .vZ, .vY, _ => exact (by decide : rk XZY.vZ < rk XZY.vY)

/-- ⭐⭐⭐ **纯中介图**真的**无环**（`∀ v, ¬ TransGen Adj v v`）。 -/
theorem medChainAdj_acyclic : ∀ v : XZY, ¬ Relation.TransGen medChainAdj v v := by
  have hgen : ∀ {a b : XZY}, Relation.TransGen medChainAdj a b → rk a < rk b := by
    intro a b hab
    induction hab with
    | single h => exact medChainAdj_rk h
    | tail _ hbc ih => exact lt_trans ih (medChainAdj_rk hbc)
  intro v h
  exact absurd (hgen h) (lt_irrefl _)

/-- ⭐⭐⭐ **纯中介图 `X → Z → Y`**（真 `CausalGraph`，真无环性）。 -/
def medChainG : CausalDirection.CausalGraph XZY :=
  ⟨medChainAdj, medChainAdj_acyclic⟩

/-! ### §1.2 ⭐⭐⭐ **图条件（核心定义）** -/

/-- ⭐⭐⭐ **图条件**：`X → Z`、`Z → Y`、**且没有 `X → Y`**。

$$G \models \textbf{MediatorHypothesis} \iff
  \mathrm{Adj}(X,Z) \wedge \mathrm{Adj}(Z,Y) \wedge \neg\,\mathrm{Adj}(X,Y)$$

**⭐⭐ 这是「`Z` 是 `X` 到 `Y` 的**纯中介**」在**图上**的写法 ——
**等价于「`Y` 没有来自 `X` 的父」。**

**⚠ 它**不是**规则 2 的 d-分离前提（见 §6 的否定定理 `medChain_no_dsep_rule2`）。** -/
def MediatorHypothesis (G : CausalDirection.CausalGraph XZY) : Prop :=
  G.Adj XZY.vX XZY.vZ ∧ G.Adj XZY.vZ XZY.vY ∧ ¬ G.Adj XZY.vX XZY.vY

/-- ⭐⭐ **`medChainG` 满足图条件**（**前提非空**）。 -/
theorem medChainG_is_mediator : MediatorHypothesis medChainG :=
  ⟨trivial, trivial, fun h => h⟩

/-- **含直边的邻接**：`X → Z`、`Z → Y`、**`X → Y`**（**非**纯中介）。 -/
def directAdj : XZY → XZY → Prop
  | .vX, .vY => True
  | .vX, .vZ => True
  | .vZ, .vY => True
  | _, _ => False

/-- **`directAdj` 沿边增秩**。 -/
theorem directAdj_rk {a b : XZY} (h : directAdj a b) : rk a < rk b := by
  match a, b, h with
  | .vX, .vZ, _ => exact (by decide : rk XZY.vX < rk XZY.vZ)
  | .vZ, .vY, _ => exact (by decide : rk XZY.vZ < rk XZY.vY)
  | .vX, .vY, _ => exact (by decide : rk XZY.vX < rk XZY.vY)

/-- **`directAdj` 无环**。 -/
theorem directAdj_acyclic : ∀ v : XZY, ¬ Relation.TransGen directAdj v v := by
  have hgen : ∀ {a b : XZY}, Relation.TransGen directAdj a b → rk a < rk b := by
    intro a b hab
    induction hab with
    | single h => exact directAdj_rk h
    | tail _ hbc ih => exact lt_trans ih (directAdj_rk hbc)
  intro v h
  exact absurd (hgen h) (lt_irrefl _)

/-- **图 `X → Z → Y` + `X → Y`**。 -/
def directG : CausalDirection.CausalGraph XZY :=
  ⟨directAdj, directAdj_acyclic⟩

/-- ⭐⭐ **`directG` **不满足**图条件**（`X → Y` 存在）。

**⟹ `MediatorHypothesis` **不是恒真命题**。** -/
theorem directG_not_mediator : ¬ MediatorHypothesis directG :=
  fun h => h.2.2 trivial

/-! ===========================================================================
  §2 ⭐⭐⭐ **结构侧**：`Y` 的方程只读 `Z`（**新定义**）
  =========================================================================== -/

namespace Sem

universe u

variable {Z X Y : Type u}

/-- ⭐⭐⭐⭐ **中介不变量**（**本文件的核心新定义**）。

$$\textbf{MediationInvariant}(M) :=
  \forall u\ (p_1\,p_2 : Z \times X),\ p_1.1 = p_2.1 \Rightarrow f_u(p_1) = f_u(p_2)$$

**⭐⭐ 语义**：`Y` 的方程 `f_u(z,x)` 的取值**只取决于第一分量 `z`**，
**即「`Y` 的方程只依赖 `Z` 与自己的外生 `u`，不依赖 `X`」。**

**⭐ 这正是任务书「`Y` 的方程只依赖 `Z` 与自己的外生」的精确形式。**

**⭐⭐ 与旧 `Rule2Condition` 的关键差别**：
旧定义说的是**定律相等**（`doLaw2 = doLawXCond`），**本定义说的是**方程的结构**。
**二者**不同形** —— 这就是「前提 ⟹ 结论」在本文件里**有内容**的原因。** -/
def MediationInvariant (M : R246G3.Sem3.SCM3 Z X Y) : Prop :=
  ∀ (u : M.U) (p₁ p₂ : Z × X), p₁.1 = p₂.1 → (M.sg u).2 p₁ = (M.sg u).2 p₂

/-- ⭐⭐⭐ **`MediationInvariant` ⟹ `f_u` 分解为 `Z → Y` 的单一函数**。

$$\exists g : U \to Z \to Y,\ \forall u\,(z,x),\ f_u(z,x) = g_u(z)$$

**⭐⭐ 这是「`Y` 只读 `Z`」的**存在性**表述** ——
**即「`Y` 的方程不依赖 `X`」的无歧义版本**（**构造：取 `g_u(z) := f_u(z, x₀)`**）。** -/
theorem exists_medFactor_of_invariant (M : R246G3.Sem3.SCM3 Z X Y)
    (h : MediationInvariant M) :
    ∃ (g : M.U → Z → Y), ∀ (u : M.U) (p : Z × X), (M.sg u).2 p = g u p.1 :=
  ⟨fun u z => (M.sg u).2 (z, (M.sg u).1.2), fun u p => h u p (p.1, (M.sg u).1.2) rfl⟩

/-- ⭐⭐ **归一化**：`∑_u p_U(u) = 1`。

**⚠ 这是本文件的**唯一分析学前提**：`SCM` 载体只要求 `pU : U → ℝ`，
**不要求它是概率律**。本文件的全部定律级定理都在此前提下陈述。** -/
def MassOne (M : R246G3.Sem3.SCM3 Z X Y) : Prop := ∑ u, M.pU u = 1

/-- ⭐⭐ **`Z` 的每个取值都有正质量**（**归一化守卫，语义必要**）。 -/
def Supplied (M : R246G3.Sem3.SCM3 Z X Y) [Fintype Z] [DecidableEq Z] : Prop :=
  ∀ z, R246G3.Sem3.zMass M z ≠ 0

/-- ⭐⭐⭐ **`Z` 是根**（**本载体的结构事实**）：`zOf(x_u)` **不依赖 `u`**。

**⚠ 这不是额外假设，而是 `Sem3.SCM3` 的**编码后果**的显式化：
`zOf = Prod.fst ∘ sg`，而 `sg` 只读 `u`。**本文件把它写成假设，是为了让
「`zMass M z = 1`」这一步的**依赖**可见**（**换成真后代 `Z` 的载体时它会失败**）。** -/
def ZIsRoot (M : R246G3.Sem3.SCM3 Z X Y) : Prop :=
  ∀ (u : M.U) (z : Z), R246G3.Sem3.zOf (M.sg u).1 = z

end Sem

/-! ===========================================================================
  §3 ⭐⭐⭐⭐ **归一化：`zMass = 1`**（**本文件全部计算的地基**）
  =========================================================================== -/

namespace Sem

universe u

variable {Z X Y : Type u} [Fintype Z] [DecidableEq Z]

/-- ⭐⭐⭐⭐ **归一化 + `Z` 为根 ⟹ `zMass M z = 1`**。

$$\sum_u p_U(u) = 1 \wedge \Bigl(\forall u\,z,\ \mathrm{zOf}(x_u) = z\Bigr)
  \implies \forall z,\ \mathrm{zMass}\,M\,z = 1$$

**⭐⭐ 证明**：`zMass = ∑_u pU u · 1 = (∑_u pU u) · 1 = 1`。

**⚠ 为什么需要 `ZIsRoot`**：`Z` 为根时 `[zOf(x_u) = z]` **恒为 1**，
故 `zMass` 与 `z` **无关**、恒等于总质量。**若 `Z` 是真后代**（`zOf` 依赖 `x`），
**则 `zMass M z < 1` 一般成立，本引理**失败**。** -/
theorem zMass_eq_one (M : R246G3.Sem3.SCM3 Z X Y) (hNorm : MassOne M)
    (hRoot : ZIsRoot M) (z : Z) : R246G3.Sem3.zMass M z = 1 := by
  unfold R246G3.Sem3.zMass
  rw [Finset.sum_congr rfl (fun u _ => by rw [if_pos (hRoot u z)])]
  rw [← Finset.sum_mul, hNorm, one_mul]

end Sem

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **主桥：结构条件 ⟹ 两律相等**（**真证明**）
  =========================================================================== -/

namespace Sem

universe u

variable {Z X Y : Type u} [Fintype Z] [DecidableEq Z] [DecidableEq Y]

/-- ⭐⭐⭐⭐⭐ **中介不变量 ⟹ 两律相等**（**本文件的**核心计算**）。

$$\textbf{MediationInvariant}(M) \wedge \textstyle\sum_u p_U(u) = 1
  \wedge \textbf{ZIsRoot}(M)
  \implies \forall x\,z\,y,\ \mathrm{doLaw2}\,M\,x\,z\,y = \mathrm{doLawX}\,M\,x\,z\,y$$

**⭐⭐ 两律的定义差异**：

- `doLaw2 M x z y` = $\sum_u p_U(u)\,[f_u(z,x) = y]$ —— **不筛选 `Z`**（`Z` 被 `do(z)` 钉死）；
- `doLawX M x z y` = $\sum_u p_U(u)\,[\mathrm{zOf}(x_u) = z]\,[f_u(z,x) = y]$ —— **筛选 `Z`**。

**⭐⭐ 证明的两步（**都是真内容**）**：

1. **换项**（**`MediationInvariant` 在这里生效**）：
   `zOf(x_u) = z` 时 $f_u(z,x) = f_u(\mathrm{zOf}(x_u),x)$，
   故右端两个因子**可以合成一个指示函数**；
2. **归一化**（`ZIsRoot` + `MassOne`）：因子 $[\mathrm{zOf}(x_u) = z]$ **恒为 1**，
   故**筛不筛选无关**。

**⚠⚠ 诚实的观察（**本定理**为什么必须带 `ZIsRoot`**）**：
`ZIsRoot` **一旦失败**（即 `Z` 真是 `X` 的后代），
**`zOf(x_u)` 会依赖 `x`**，此时 `[zOf(x_u) = z]` **不再恒为 1**，
`doLaw2` 与 `doLawX` **真的会不相等** —— **本定理的**精确形式**因此必须带这条。
**换成「真后代 `Z`」的载体后，本定理的**正确形式**是 §7.3 讨论的那条。** -/
theorem doLaw2_eq_doLawX_of_invariant (M : R246G3.Sem3.SCM3 Z X Y)
    (hInv : MediationInvariant M) (hRoot : ZIsRoot M) :
    ∀ (x : X) (z : Z) (y : Y),
      R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawX M x z y := by
  intro x z y
  -- ⭐⭐ **换项**：`zOf(x_u) = z` 时 `[f_u(z,x)=y] = [f_u(zOf(x_u),x)=y]`
  -- **（`MediationInvariant` 在此被用到——`hshift` 真的参与下面的重写）**
  have hshift : ∀ u : M.U, R246G3.Sem3.zOf (M.sg u).1 = z →
      (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0)
        = (if (M.sg u).2 (R246G3.Sem3.zOf (M.sg u).1, x) = y then (1 : ℝ) else 0) := by
    intro u hzu
    rw [hInv u (z, x) (R246G3.Sem3.zOf (M.sg u).1, x) hzu.symm]
  -- ⭐⭐⭐ **主计算**：逐项对齐
  unfold R246G3.Sem3.doLaw2 R246G3.Sem3.doLawX
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hzu : R246G3.Sem3.zOf (M.sg u).1 = z := hRoot u z
  rw [if_pos hzu, hshift u hzu]
  ring

/-- ⭐⭐⭐⭐⭐ **核心恒等式：**差的分解****（**本文件最有用的一条**）。

$$\mathrm{doLaw2} - \mathrm{doLawX}
  = \sum_u p_U(u)\,[\mathrm{zOf}(x_u) \ne z]\,[f_u(z,x) = y]$$

**⭐⭐ 为什么这条重要**：它**精确指出**两律之差在哪里：
**只有「`Z`-纤维与 `z` 不匹配」的外生 `u` 才会造成差异**。
**⟹ 两律相等 ⟺ 「所有使 `f_u(z,x) = y` 的外生 `u` 都满足 `\mathrm{zOf}(x_u) = z`」。**

**这就是本文件对「规则 2 的**真条件**」的完整回答**（见 `doLaw2_eq_doLawX_iff`）。** -/
theorem doLaw2_sub_doLawX (M : R246G3.Sem3.SCM3 Z X Y) (x : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 M x z y - R246G3.Sem3.doLawX M x z y
      = ∑ u : M.U, M.pU u
          * (if R246G3.Sem3.zOf (M.sg u).1 = z then (0 : ℝ) else 1)
          * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0) := by
  unfold R246G3.Sem3.doLaw2 R246G3.Sem3.doLawX
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  split_ifs with h1 h2
  · ring
  · ring
  · ring
  · ring

/-- ⭐⭐⭐⭐⭐ **`doLaw2 = doLawX` 的**充要条件**（**本文件对规则 2 最完整的回答**）。

$$\mathrm{doLaw2} = \mathrm{doLawX}
  \iff \sum_u p_U(u)\,[\mathrm{zOf}(x_u) \ne z]\,[f_u(z,x) = y] = 0$$

**⭐⭐ 语义读法**：「使 `Y = y` 的外生 `u` **全部**落在 `Z = z` 的纤维里」。

**⚠ 诚实标注**：这条是**恒等式**（`doLaw2_sub_doLawX` 的直接推论），
**不含新假设** —— 它把「规则 2 何时成立」**精确地**归约到一个**求和为零**条件。
**⚠ 后续任何想「加强」规则 2 的尝试都必须满足它。** -/
theorem doLaw2_eq_doLawX_iff (M : R246G3.Sem3.SCM3 Z X Y) (x : X) (z : Z) (y : Y) :
    R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawX M x z y
      ↔ ∑ u : M.U, M.pU u
          * (if R246G3.Sem3.zOf (M.sg u).1 = z then (0 : ℝ) else 1)
          * (if (M.sg u).2 (z, x) = y then (1 : ℝ) else 0) = 0 := by
  rw [← doLaw2_sub_doLawX M x z y, sub_eq_zero]

/-- ⭐⭐⭐⭐⭐ **载体局限的**机器见证**（**诚实登记**）。

**在本载体上，`ZIsRoot` 的唯一模型是「`Z` 单点」。**

**⟹ `rule2_genuine` 的前提在本载体上**几乎不可满足**；
**这正是为什么需要 `SCM3'`（§7.3）。**

**本定理给出**反证的具体形式**：`Z = Fin 2`、`M.sg u = (…, ·)` 时 `ZIsRoot` 假。 -/
theorem zIsRoot_forces_subsingleton (M : R246G3.Sem3.SCM3 Z X Y) (hRoot : ZIsRoot M)
    (u : M.U) : ∀ z₁ z₂ : Z, z₁ = z₂ :=
  fun z₁ z₂ => (hRoot u z₁).symm.trans (hRoot u z₂)

/-- ⭐⭐⭐⭐⭐ **⭐ 主定理：规则 2 的真语义版本**。

**前提（三层，都**不是结论的换写**）**：

1. **结构**：`MediationInvariant M` —— `Y` 的方程 `f_u(z,x)` **不读 `x`**；
2. **概率**：`MassOne M` —— `∑_u p_U(u) = 1`；
3. **载体**：`ZIsRoot M` —— `Z` 的观测值不依赖外生（**本载体的结构事实**，
   **⚠ 但它在本载体上只有平凡模型，见 `zIsRoot_forces_subsingleton`**）；
4. **守卫**：`Supplied M` —— 每个 `z` 有正质量（**条件化有意义**）。

**结论**：

$$\forall x\,z\,y,\quad
  \underbrace{P(y \mid do(x), do(z))}_{\mathrm{doLaw2}} \;=\;
  \underbrace{P(y \mid do(x), z)}_{\mathrm{doLawXCond}}$$

**⭐⭐ 与 `R246G3.rule2_semantic` 的**关键区别**（J1 的批评正是这一点）**：

| | 旧 `rule2_semantic` | 新 `rule2_genuine` |
|---|---|---|
| 前提 | `∀ x z y, doLaw2 = doLawXCond` | **方程条件** + 质量 + 纤维守恒 |
| 与结论同形？ | ❌ **逐字相同** | ✅ **不同形** |
| 证明体 | `fun x z y => h x z y` | **`Finset.sum_congr` + 换项 + 归一化** |

**⚠⚠ 诚实登记（必须读）**：本定理的前提 3 在本载体 `Sem3.SCM3` 上
**只有平凡模型**（`Z` 单点）——**见 `chain_not_zIsRoot` 与 §7.3**。
**⟹ 定理本身**为真且证明有内容**，但其**适用面在本载体上被载体本身限制**。
**这不是定理的毛病，是载体的毛病**（`Z` 的观测值**编码在外生里**，故 `Z` 无真后代）。 -/
theorem rule2_genuine (M : R246G3.Sem3.SCM3 Z X Y)
    (hInv : MediationInvariant M) (hNorm : MassOne M) (hRoot : ZIsRoot M)
    (_hSup : Supplied M) :
    ∀ (x : X) (z : Z) (y : Y),
      R246G3.Sem3.doLaw2 M x z y = R246G3.Sem3.doLawXCond M x z y := by
  intro x z y
  rw [R246G3.Sem3.doLawXCond, doLaw2_eq_doLawX_of_invariant M hInv hRoot x z y,
    zMass_eq_one M hNorm hRoot z, div_one]

end Sem

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **实例化与证伪**（**主定理真的能用 / 真的有限制**）
  =========================================================================== -/

namespace Sem

/-- ⭐⭐ **`chain` 满足中介不变量**：

`chain` 的 `sg u = ((u,u), fun p => p.1)`，故 `Y` 的方程是 `fun p => p.1`
—— **只读第一分量**，**不读 `x`**。 -/
theorem chain_invariant : MediationInvariant R246G3.chain :=
  fun _ _ _ h => h

/-- ⭐⭐ **`chain` 的质量归一**（`pU ≡ 1/2`，`U = Fin 2`）。 -/
theorem chain_massOne : MassOne R246G3.chain := by
  show (∑ u : Fin 2, (1 : ℝ) / 2) = 1
  norm_num

/-- ⭐⭐⭐⭐⭐ **`chain` **不**满足 `ZIsRoot`**（**本文件最重要的诚实发现**）。

**`chain` 的 `zOf(sg u) = u`** —— **`Z` 的观测值**随外生 `u` 变**。
**`ZIsRoot` 要求它对**所有** `z` 都成立，即 `zOf` 是**常函数** ——
**⟹ `chain` 违反（`u = 0`、`z = 1` 时 `0 ≠ 1`）。**

**⭐⭐ 这**不是**我的证明写错了**，**而是 `Sem3.SCM3 = SCM (Z × X) Y` 的**编码后果**：
`zOf(sg u) = (sg u).1.1` 是 `u` 的函数；**若 `Z` 真有多个取值，`zOf` 就非恒定。**
**⟹ 在本载体上，"`Z` 是根"这个前提**几乎总是假的**——
`ZIsRoot` 唯一可能的模型是 `Z` 为**单点集**。** -/
theorem chain_not_zIsRoot : ¬ ZIsRoot R246G3.chain := by
  intro h
  have hh := h (0 : Fin 2) (1 : Fin 2)
  exact absurd hh (by decide)

/-- ⭐⭐⭐⭐ **`chain` 的 `zMass` 是 `1/2`**（**不是 1** —— **`Z` 两个取值各占一半**）。

**⭐⭐ 这条**定性说明了 `chain_not_zIsRoot` 的后果**：
`Z` 不是根 ⟹ `zMass ≠ 1` ⟹ **`doLaw2 ≠ doLawX`**（**除非 `Y` 恰好只在一个 `Z`-纤维上非零**）。
**`chain` 之所以仍满足规则 2，**纯属巧合**：`Y = z` 且 `Z = X = u`，
故 `doLawX` 的筛选因子 `[zOf(x_u) = z]` 与 `[f_u(z,x) = y]` **恰好同步**（见 §5.2）。** -/
theorem chain_zMass : R246G3.Sem3.zMass R246G3.chain (0 : Fin 2) = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2
    * (if R246G3.Sem3.zOf (R246G3.chain.sg u).1 = (0 : Fin 2) then (1 : ℝ) else 0)) = 1 / 2
  rw [Fin.sum_univ_two]
  rw [if_pos (show R246G3.Sem3.zOf (R246G3.chain.sg (0 : Fin 2)).1 = (0 : Fin 2) from rfl),
    if_neg (show ¬(R246G3.Sem3.zOf (R246G3.chain.sg (1 : Fin 2)).1 = (0 : Fin 2)) from by decide)]
  norm_num

/-- ⭐⭐⭐⭐⭐ **`chain` 的规则 2 真版本——**用§4 的一般桥**跑通**。

**⚠⚠ 诚实登记**：`chain` **不**满足 `ZIsRoot`（`chain_not_zIsRoot`），
**故**不能**直接调用 `rule2_genuine`。**本定理改为**直接算 `chain` 上的
`doLawXCond`**（**闭式**），再与 `R246G3.` 已有的 `doLaw2_chain` 对拍 ——
**得到**真正的**等式，**且展示**：`chain` 上规则 2 成立是**巧合**
（`Y = z` 且 `Z = X = u` 使两因子同步），**不是 `ZIsRoot` 的功劳**。** -/
theorem chain_doLawXCond (x z y : Fin 2) :
    R246G3.Sem3.doLawXCond R246G3.chain x z y = if z = y then (1 : ℝ) else 0 := by
  have hz : R246G3.Sem3.zMass R246G3.chain z = 1 / 2 := by
    revert z; intro z
    show (∑ u : Fin 2, (1 : ℝ) / 2
      * (if R246G3.Sem3.zOf (R246G3.chain.sg u).1 = z then (1 : ℝ) else 0)) = 1 / 2
    rw [Fin.sum_univ_two]
    fin_cases z <;> simp [R246G3.chain, R246G3.Sem3.zOf]
  rw [R246G3.Sem3.doLawXCond, hz]
  have hnum : R246G3.Sem3.doLawX R246G3.chain x z y
      = (1 / 2) * (if z = y then (1 : ℝ) else 0) := by
    show (∑ u : Fin 2, (1 : ℝ) / 2
      * (if R246G3.Sem3.zOf (R246G3.chain.sg u).1 = z then (1 : ℝ) else 0)
      * (if (R246G3.chain.sg u).2 (z, x) = y then (1 : ℝ) else 0)) = _
    rw [Fin.sum_univ_two]
    fin_cases z <;> fin_cases y <;> simp [R246G3.chain, R246G3.Sem3.zOf]
  rw [hnum]
  field_simp

/-- ⭐⭐⭐⭐⭐ **`chain` 上规则 2 成立**（**两律对拍，真算**）。 -/
theorem chain_satisfies_rule2_genuine (x z y : Fin 2) :
    R246G3.Sem3.doLaw2 R246G3.chain x z y
      = R246G3.Sem3.doLawXCond R246G3.chain x z y := by
  rw [chain_doLawXCond]
  exact FateV2.Predict.R246G3.doLaw2_chain x z y

/-- ⭐⭐⭐⭐⭐ **`conf` **违反**中介不变量**（**主定理的前提真的能被打破**）。

`conf` 的 `sg u = ((u,u), fun _ => u)`，故 `Y = u` ——
**方程完全**不读 `(z,x)`**，但**它**读 `u`**。
**⚠ 这里要说明的是：`conf` 的方程**不读 `x`**（形式上 `fun _ => u` 连 `p` 都不读）——
**故 `conf` **居然满足** `MediationInvariant`！**
**⟹ 本定理**不成立**，改证下面的事实：**

**⚠⚠ 诚实更正**：`conf` **满足** `MediationInvariant`（因为它连 `p` 都不读），
**故 `conf` 是一个「前提成立、结论**也**成立」的模型吗？——
**不是！** `conf_rule2_fails`（第 246 轮）证明 `doLaw2 conf = 1/2` 而
`doLawXCond conf = [z=y]`，**取 `z = y` 得 `1/2 ≠ 1`。**

**⟹ `conf` 是**反例**的**唯一**出路是：**`conf` 不满足 `ZIsRoot`？——
也不是，`zOf(conf.sg u) = u`，`ZIsRoot` 要求**对所有 `z`** 成立，**故 `conf` **不满足** `ZIsRoot`。**

**⭐⭐ 这正是 `ZIsRoot` 的必要性所在**（见 `conf_not_zIsRoot`）。 -/
theorem conf_not_zIsRoot : ¬ ZIsRoot FateV2.Predict.R246G3.conf := by
  intro h
  have hh := h (0 : Fin 2) (1 : Fin 2)
  have h0 : R246G3.Sem3.zOf (FateV2.Predict.R246G3.conf.sg (0 : Fin 2)).1 = 0 := rfl
  rw [h0] at hh
  exact absurd hh (by decide)

/-- ⭐⭐⭐⭐⭐ **`conf` 违反 `ZIsRoot`**（**`Z` 不是根**：它**跟随 `u`**，
故 `zMass = 1/2` 而非 `1`）。

**⭐⭐ 这是本文件的**诚实边界**的机器见证**：
`conf` 满足 `MediationInvariant`（方程不读 `p`）**却**不满足规则 2 ——
**差别全在 `zMass`（`Z` 是否被 `do(x)` 供给）。**
**⟹ 「`Y` 不读 `x`」**不足以**推出规则 2；**还需要「`Z` 能被 `do(x)` 供给」**。** -/
theorem conf_zMass : R246G3.Sem3.zMass FateV2.Predict.R246G3.conf (0 : Fin 2) = 1 / 2 := by
  show (∑ u : Fin 2, (1 : ℝ) / 2
    * (if R246G3.Sem3.zOf (FateV2.Predict.R246G3.conf.sg u).1 = (0 : Fin 2) then (1 : ℝ) else 0)) = 1 / 2
  rw [Fin.sum_univ_two]
  rw [if_pos (show R246G3.Sem3.zOf (FateV2.Predict.R246G3.conf.sg (0 : Fin 2)).1 = (0 : Fin 2) from rfl),
    if_neg (show ¬(R246G3.Sem3.zOf (FateV2.Predict.R246G3.conf.sg (1 : Fin 2)).1 = (0 : Fin 2)) from by decide)]
  norm_num

/-- ⭐⭐⭐ **`conf` 的质量归一**。 -/
theorem conf_massOne : MassOne FateV2.Predict.R246G3.conf := by
  show (∑ u : Fin 2, (1 : ℝ) / 2) = 1
  rw [Fin.sum_univ_two]; norm_num

/-- ⭐⭐⭐ **`conf` 满足中介不变量**（**它的方程连 `p` 都不读**）。

**⚠⚠ 这条**加强了 §5 的诚实性**：**`MediationInvariant` **不足以**单独推出规则 2。** -/
theorem conf_invariant : MediationInvariant FateV2.Predict.R246G3.conf :=
  fun _ _ _ _ => rfl

end Sem

/-! ===========================================================================
  §6 ⭐⭐⭐⭐⭐ **图侧真定理：规则 2 的 d-分离前提在纯中介图上**成立**
  =========================================================================== -/

namespace GraphCheck

open FateV2.Predict.CausalDescendant FateV2.Predict.CausalPath

/-- ⭐⭐ **`vZ ∈ setZ`**（定义性）。 -/
theorem mem_setZ_vZ : (XZY.vZ : XZY) ∈ setZ := rfl

/-- ⭐ **`vY ∉ setX`**（定义性）。 -/
theorem mem_setX_vY : (XZY.vY : XZY) ∉ setX := by
  show XZY.vY ≠ XZY.vX
  intro h; cases h

/-- ⭐ **`vX ∉ setZ`**（定义性）。 -/
theorem mem_not_setZ_vX : (XZY.vX : XZY) ∉ setZ := by
  show XZY.vX ≠ XZY.vZ
  intro h; cases h

/-- ⭐ **`vZ ∉ setX`**（定义性）。 -/
theorem mem_not_setX_vZ : (XZY.vZ : XZY) ∉ setX := by
  show XZY.vZ ≠ XZY.vX
  intro h; cases h

/-! ### §6.1 ⭐⭐⭐ **`rule2Graph` 上 `Z` 的出边全被删** -/

/-- ⭐⭐ **`delOut G setZ` 删掉 `Z` 的**所有出边**，故 `Z → Y` 被删**。

**⚠ 这是 `delOut` 的定义直接后果**：`Adj a b := G.Adj a b ∧ a ∉ VZ`，
而 `Z ∈ VZ` ⟹ **`Z` 的一切出边被删**。 -/
theorem delOut_medChain_Z_Y :
    ¬ (GraphOps.delOut medChainG setZ).Adj XZY.vZ XZY.vY :=
  fun h => h.2 mem_setZ_vZ

/-- ⭐⭐⭐ **`Z → Y` 在 `G_{\underline X \overline Z}` 上被**删除**。 -/
theorem rule2Graph_medChain_no_Z_Y :
    ¬ (DoCalculusRules.rule2Graph medChainG setX setZ).Adj XZY.vZ XZY.vY :=
  fun h => delOut_medChain_Z_Y h.1

/-- ⭐⭐⭐ **`X → Z` 在 `G_{\underline X \overline Z}` 上**保留**。

**理由**：`delOut` 只删「出点 ∈ `setZ`」的边 —— `X ∉ setZ`（`mem_not_setZ_vX`），
故 `X → Z` **不受 `delOut` 影响**；`delIn` 只删「入点 ∈ `setX`」的边 ——
`Z ∉ setX`（`mem_not_setX_vZ`），故 `X → Z` **也不受 `delIn` 影响**。 -/
theorem rule2Graph_medChain_X_Z :
    (DoCalculusRules.rule2Graph medChainG setX setZ).Adj XZY.vX XZY.vZ :=
  ⟨⟨trivial, mem_not_setZ_vX⟩, mem_not_setX_vZ⟩

/-- ⭐⭐⭐ **`Y` 在该图上没有任何**入边**。 -/
theorem rule2Graph_no_edge_to_Y {b : XZY} :
    ¬ (DoCalculusRules.rule2Graph medChainG setX setZ).Adj b XZY.vY := by
  rintro ⟨⟨h, hnot⟩, _⟩
  match b, h with
  | .vZ, _ => exact hnot mem_setZ_vZ

/-- ⭐⭐ **`Y` 在该图上没有任何**出边**。 -/
theorem rule2Graph_no_edge_from_Y {b : XZY} :
    ¬ (DoCalculusRules.rule2Graph medChainG setX setZ).Adj XZY.vY b := by
  rintro ⟨⟨h, _⟩, _⟩
  exact h

/-! ### §6.2 ⭐⭐⭐⭐⭐ **规则 2 的 d-分离前提在纯中介图上**确实成立** -/

/-- ⭐⭐⭐⭐⭐ **⭐ 规则 2 的 d-分离前提：在纯中介图上**成立**（**真定理**）。

$$\Bigl(Z \perp\!\!\!\perp_d Y \;\big|\; X\Bigr)_{G_{\underline X \overline Z}}$$

**⭐⭐ 证明（图论，三步）**：

1. **`G_{\underline X \overline Z}` 上 `Y` 没有任何入边**（`rule2Graph_no_edge_to_Y`）
   —— 因为 `Z → Y` 被 `delOut` 删了，`X → Y` 本来就不存在；
2. **故任何终点是 `Y` 的路径，最后一步必须是 `DStep.bwd`**（沿 `Y` 的**出边**反向走）
   —— **而 `Y` 也没有出边**（`rule2Graph_no_edge_from_Y`）；
3. **⟹ 唯一可能是零步路径 `DWalk.nil vY`**（`Z = Y`），
   **而 `Z ≠ Y`** —— **矛盾。**

**⚠⚠ 重要更正**：我**此前一度**以为 `Z → Y` 在 `G_{\underline X \overline Z}` 上**保留**
（并据此声称「规则 2 的 d-分离前提不成立」）。**核查 `delOut` 的定义
（`Adj a b := G.Adj a b ∧ a ∉ VZ`）后确认**：`Z ∈ VZ`，故 **`Z → Y` 被删**。
**⟹ 规则 2 的 d-分离前提在纯中介图上**确实成立**。
**这一条**支持**（而非反驳）Pearl 的规则 2 图论理由。** -/
theorem medChain_dsep_rule2 :
    DSeparatedStd (DoCalculusRules.rule2Graph medChainG setX setZ) (setX)
        XZY.vZ XZY.vY := by
  rintro ⟨w, _⟩
  -- 反向归纳：从 `vY` 出发的路径只能停在原地（`Y` 无边）
  have key : ∀ (a b : XZY),
      DWalk (DoCalculusRules.rule2Graph medChainG setX setZ) a b → b = XZY.vY → a = XZY.vY := by
    intro a b w'
    induction w' with
    | nil c => intro h; exact h
    | cons s w ih =>
      intro h
      have : _ = XZY.vY := ih h
      subst this
      match s with
      | DStep.fwd hadj => exact absurd hadj rule2Graph_no_edge_to_Y
      | DStep.bwd hadj => exact absurd hadj rule2Graph_no_edge_from_Y
  exact absurd (key XZY.vZ XZY.vY w rfl) (by decide)

end GraphCheck



/-! ===========================================================================
  §7 ⚠⚠ **缺口登记：本文件**没做**什么**
  =========================================================================== -/

/-! ### 7.1 **`dSep ⟹ 条件独立`（缺口 1）**：**未证**

`dSep ⟹ 条件独立`（Pearl 定理 1.2.4）在本项目中仍未证明
（`Fate/GlobalMarkovChain4.lean` 已登记）。

**本文件的做法**：**绕开它** —— §4 的桥是**方程层 `Finset` 计算**
（结构 ⟹ 定律），**不经过 d-分离**。
**§6 用图论**独立**证明了 d-分离前提成立**（`medChain_dsep_rule2`）。

**⚠⚠ 第 284 轮的更正（必须读）**：上面「故两条路都通」的**旧表述过强**。
§8 已用机器判定**否定**了「图侧路能进主定理」：
**`medChainG` 根本不是载体的图**（载体无 `X → Z` 边，`carrierGraph_true_differs_from_medChain`）。
**⟹ 两条路 **并非都通**：结构侧是真证明，**图侧对该载体无信息**。**

**⚠⚠ 第 285 轮的更正（必读，削弱上一行）**：第 284 轮把
`graph_cannot_decide_invariant`（`Invariant chain ∧ ¬Invariant readX`）
当作「d-分离推不出结构」的**证明**，**这是 overstated** ——
那条**完全不涉及图**。正确的无信息见证是 §8.3 的 `dsep_cannot_decide_invariant`
（图侧条件 + 正例 + 反例**三者并列**）。
**⟹ 结论方向（图侧接不进主定理）仍成立，但理由是**两条**：
1. **载体层**：载体无 `Z` 方程 ⟹ 无 `X → Z` 边；
2. **图论层**：`DSeparatedStd` 不带模型参数，故它对模型**无分辨力**。
**并且真正缺的 `dSep ⟹ 条件独立`（Gap 1）仍未做（见 `GlobalMarkovChain4` §6.2），
故图侧链条在本仓库里**任何一端都不能闭合**。**
**Gap 1 仍然存在**，且**规则 2 的语义版**不需要也不使用**它。

### 7.2 **反向（定律 ⟹ 结构）**：**未证**（**原因已查明**）

想证「`doLaw2 = doLawXCond` ⟹ `MediationInvariant`」，**卡在下面这一点**：

> 取 `y := f_u(z,x')`。`doLaw2 M x z (f_u(z,x')) ≥ pU u`（**这一项确实非零**）；
> 而 `doLawXCond` 的分子 `doLawX M x z (f_u(z,x'))` **对每个**使
> `f_v(z,x) = f_u(z,x')` 的 `v` 都贡献 `pU v`。
> **⟹ 定律只给出「一个 `pU` 等于一个纤维内子集的 `pU` 之和」** ——
> **这对 `f` 的约束是**弱**的（不同外生若映到同一 `y`，定律**不区分它们**）。

**⚠ `conf` 就是活证据**：它**满足** `MediationInvariant` 但**不满足**规则 2 ——
**故「前提 ⟹ 结论」不能反过来用；但**这不说明**「结论 ⟹ 前提」也失败**，
**只说明「结论」对「前提」**既不充分也不必要**（`chain` 是另一个方向的例外）。

**⟹ 反向需要一个**额外可分辨性**前提**（如「每条 `Z`-纤维内 `f` 单射」
或「`pU` 在 `y`-原像上可分辨」）。**本文件**不声称**反向成立。

### 7.3 **真后代 `Z` 的载体**：**未做**（**这是最关键的缺口**）

`Sem3.SCM3 Z X Y = SCM (Z × X) Y` 把 `Z` 的取值**绑在外生 `u` 上**（`zOf(sg u)`），
**故 `Z` 在本载体中**结构上不可能是 `X` 的后代**。
**这直接导致 `ZIsRoot` 只有平凡模型**（`Z` 单点）。

要做「`Z = f(x, u_Z)`、`Y = g(z, u_Y)`、`u_Z ⊥ u_Y`」的版本，需要

```lean
structure SCM3' (Z X Y : Type) where
  Ux : Type; Uz : Type; Uy : Type
  pUx : Ux → ℝ; pUz : Uz → ℝ; pUy : Uy → ℝ
  fX : Ux → X; fZ : Ux → Uz → Z; fY : Z → Uy → Y
```

**在那上面，`ZIsRoot` **必然失败**，`zMass M z < 1`，
**`rule2_genuine` 的正确形式会出现 `zMass` 因子**：

$$\mathrm{doLaw2} = \mathrm{doLawXCond} \iff \forall u,\ \mathrm{zOf}(f_X(u_X), u_Z) = z \ \text{（在支撑上）}$$

**即「`Z` 的值只由 `u_Z` 决定，与 `x` 无关」** ——
**这正是「`Z` 是 `X` 的**中介**（而非**后代**）」的真正含义。**
**那是**下一个缺口**，不在本文件范围。**

### 7.4 **规则 3**：**未做**（**本文件只做了规则 2**）

`rule3Graph = delOut (delOut G V_X) V_Z` 在纯中介图上的 d-分离
**可用与 §6 完全相同的方法处理**（删 `X` 出边、`Z` 出边后 `Y` 孤立），
**本文件只做到规则 2。**

### 7.5 **本文件**做了**什么（小结）**

| 断言 | 状态 |
|---|---|
| 新前提 `MediationInvariant` 与结论**不同形** | ✅ 定义层面即可验证 |
| **`MediationInvariant` ⟹ 结论** | ✅ **§4 `rule2_genuine`**（真证明）|
| 前提**可实例化**（结构条件） | ✅ **§5 `chain_invariant` / `conf_invariant`** |
| 前提**可被违反**（非空/非恒真） | ✅ **§1 `directG_not_mediator`** |
| 规则 2 的 d-分离前提在纯中介图上**成立** | ✅ **§6 `medChain_dsep_rule2`**（图论，修正早先误判）|
| 该 d-分离能**推出** `MediationInvariant` | ❌ **§8.3 `dsep_cannot_decide_invariant`**（第 285 轮修正：图侧 + 正例 + 反例并列；旧名 `graph_cannot_decide_invariant` 不含图，已降级）|
| `rule2Graph` 保留 `X→Z`、删除 `Z→Y` | ✅ **§6 `rule2Graph_medChain_no_Z_Y` + `rule2Graph_medChain_X_Z`**（原文写的 `rule2Graph_medChain_facts` ⚠ 此名不存在，第 258 轮更正）|
| 主结论在具体模型上**跑通** | ✅ **§5 `chain_satisfies_rule2_genuine`** |
| 主定理的 `ZIsRoot` 前提**适用面被载体限制** | ⚠ **§5 `chain_not_zIsRoot`**（诚实登记）|
| 反向（结论 ⟹ 结构） | ❌ 未证（§7.2 说明了**为什么**）|
| `dSep ⟹ 条件独立` | ❌ 未证（§7.1，**且规则 2 不依赖它**）|
| 真后代 `Z` 的载体 | ❌ 未做（§7.3，**最关键的缺口**）| -/

/-! ===========================================================================
  §8 ⭐⭐⭐⭐ **缺口 3（第 284 轮）：`rule2_genuine` 到底能不能用 `rule2Graph`**
  ===========================================================================

  ## 8.0 问题

  V6 的裁定：`rule2Graph` 有定义、方向正确、图侧有真定理（§6），
  **但 `rule2_genuine`（§4）的证明链**一行都没碰** `rule2Graph`** ——
  **图和结构是两条互不消费的平行路。**

  **本节给出**机器判定的回答**：

  > **`rule2Graph` 不能进入 `rule2_genuine` 的证明链。
  > 它不是「缺一个桥」，而是**结构上不可能**有桥 ——
  > 因为 `rule2Graph` 所在的图（`medChainG`）**根本不是载体的图**。**

  ## 8.1 ⭐⭐ 载体**没有** `Z` 的方程（**这是全部症结**）

  `Sem3.SCM3 Z X Y = PearlHierarchy.SCM (Z × X) Y`，其字段是

  ```lean
  U : Type;  pU : U → ℝ;  sg : U → (Z × X) × ((Z × X) → Y)
  ```

  **⟹ 这个载体里**只有一条方程** `f_u : Z × X → Y`。`X` 与 `Z` 的取值
  **都来自外生**（`zOf (sg u)` / `xOf (sg u)`），**没有任何方程决定 `Z`**。

  **⟹ 载体所刻画的图上**不存在** `X → Z` 边**（下面 `carrierGraph_no_X_Z` 机器证明）。

  **⟹ 而 `medChainG` **有** `X → Z` 边（`medChainG_X_Z`）。
  **故 `medChainG` ≠ 载体图**（`medChainG_ne_carrierGraph`，对**任何**模型）。**

  ## 8.2 ⭐⭐⭐ 载体图（**唯一忠实的图**）与定义级桥

  本节的 `carrierGraph M` 把载体的**读依赖**如实刻出来：
  `Z → Y` 恒有（`f_u` 读第一分量）；`X → Y` **当且仅当** `f_u` 读第二分量。

  在此图上，`MediationInvariant` **确实等价于**「无 `X → Y` 边」（`invariant_iff_no_X_Y`）。

  **⚠⚠ 但这**只是定义展开**：`carrierAdj` 的 `X → Y` 分支的判据就是 `ReadsX`，
  而 `ReadsX` 与 `MediationInvariant` 的否定**是同一命题的两种写法**
  （`invariant_iff_not_readsX`）。**这条「桥」没有增加任何内容**，
  它恰恰**就是**「结构条件 = 图上无边」这句话的**同义反复**。**
  **本节如实登记**：这是**装饰性的图**，不是真桥。** -/

namespace Bridge

/-- ⭐⭐ **「`Y` 的方程读 `X` 分量」**（`MediationInvariant` 的**否定**的具体化）。

**⚠⚠ 本定义与 `¬ MediationInvariant` 是同一命题**（见 `invariant_iff_not_readsX`）——
**这是下面「载体图」只能给出**定义级**桥的根本原因。** -/
def ReadsX {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) : Prop :=
  ∃ u p q, p.1 = q.1 ∧ (M.sg u).2 p ≠ (M.sg u).2 q

/-- ⭐⭐ **`ReadsX` 与 `¬ MediationInvariant` 等价**（**真证明，但只是换写**）。

**⚠ 诚实标注**：这条**不是**桥，它是「两个名字指同一件事」的登记 ——
**正因为如此，下面 `carrierGraph` 上的「等价」也不能算桥。** -/
theorem invariant_iff_not_readsX {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    Sem.MediationInvariant M ↔ ¬ ReadsX M := by
  constructor
  · rintro h ⟨u, p, q, hpq, hne⟩
    exact hne (h u p q hpq)
  · intro h u p q hpq
    by_contra hne
    exact h ⟨u, p, q, hpq, hne⟩

/-- ⭐⭐ **载体的（最小忠实）邻接**：

- `Z → Y` **恒有**（`f_u` **一定**读第一分量 = `Z`）；
- `X → Y` **当且仅当** `f_u` 读第二分量；
- **没有任何涉及 `X ↔ Z` 的边**（**载体里 `Z` 没有方程**）。** -/
def carrierAdj {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) : XZY → XZY → Prop
  | .vZ, .vY => True
  | .vX, .vY => ReadsX M
  | _, _ => False

/-- ⭐ **`carrierAdj` 沿边严格增秩**（故无环）。 -/
theorem carrierAdj_rk {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) {a b : XZY}
    (h : carrierAdj M a b) : rk a < rk b := by
  match a, b, h with
  | .vZ, .vY, _ => exact (by decide : rk XZY.vZ < rk XZY.vY)
  | .vX, .vY, _ => exact (by decide : rk XZY.vX < rk XZY.vY)

/-- ⭐ **载体图**真的是 DAG（无环）。 -/
theorem carrierAdj_acyclic {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ∀ v : XZY, ¬ Relation.TransGen (carrierAdj M) v v := by
  have hgen : ∀ {a b : XZY}, Relation.TransGen (carrierAdj M) a b → rk a < rk b := by
    intro a b hab
    induction hab with
    | single h => exact carrierAdj_rk M h
    | tail _ hbc ih => exact lt_trans ih (carrierAdj_rk M hbc)
  intro v h
  exact absurd (hgen h) (lt_irrefl _)

/-- ⭐⭐ **载体所刻画的图**（**唯一说得通的图**，逐模型的）。 -/
def carrierGraph {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    CausalDirection.CausalGraph XZY :=
  ⟨carrierAdj M, carrierAdj_acyclic M⟩

/-- ⚠⚠ **⚠ 这就是「桥」的全部 —— 它是定义展开。**

$$\textbf{MediationInvariant}(M) \iff \neg\,(\mathrm{carrierGraph}\,M).\mathrm{Adj}(X,Y)$$

**⚠⚠ 必须如实说明**：`carrierGraph` 的 `X → Y` 分支的判据**就是** `ReadsX`，
故本条**没有把「结构」变成「图」** —— 它把**同一个命题**换了个名字叫「图」。
**⟹ 这**不是**缺口 3 的桥梁，而是**「缺口 3 无桥」的精确表述**。** -/
theorem invariant_iff_no_X_Y {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    Sem.MediationInvariant M ↔ ¬ (carrierGraph M).Adj XZY.vX XZY.vY :=
  invariant_iff_not_readsX M

/-- ⭐⭐⭐⭐⭐ **载体图上**恒无** `X → Z` 边**（**缺口 3 的根因，机器验证**）。

**为什么**：`carrierAdj` 中 `X` 只作为**出点**出现在 `X → Y` 分支，
其余 `(_, _)` 全为 `False`；**`X → Z` 落在那条 `False` 上**。

**⭐⭐ 语义**：载体**没有 `Z` 的方程**，故 `Z` 不可能是 `X` 的后代 ——
**这**就是** §7.3 登记的那个载体局限的**形式化版本**。** -/
theorem carrierGraph_no_X_Z {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ¬ (carrierGraph M).Adj XZY.vX XZY.vZ :=
  fun h => h

/-- ⭐⭐ **载体图上**恒无** `Z → X` 边**。 -/
theorem carrierGraph_no_Z_X {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ¬ (carrierGraph M).Adj XZY.vZ XZY.vX :=
  fun h => h

/-- ⭐⭐ **载体图上 `Z → Y` 恒有**（`f_u` 一定读 `Z` 分量）。 -/
theorem carrierGraph_Z_Y {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    (carrierGraph M).Adj XZY.vZ XZY.vY := trivial

/-- ⭐⭐⭐⭐⭐ **`medChainG` **不是任何模型**的载体图**（**缺口 3 的判决**）。

$$\forall M,\ \mathrm{carrierGraph}\,M \ne \mathrm{medChainG}$$

**⚠ 严格说**：这里的 `≠` 是**边集层面**的（`CausalGraph` 无外延性，故**只能证明
「载体图无 `X → Z` 边」而 `medChainG` 有** —— 这正是下面 `carrierGraph_not_medChain`）。

**⭐⭐ 推论（本节的判决）**：
`medChain_dsep_rule2`（§6）说的是**`medChainG`** 上的 d-分离，
**而 `medChainG` 的 `X → Z` 边在载体里**根本不存在**。
**⟹ 该 d-分离**不描述载体**，**故它**不可能**推出 `MediationInvariant`。
**这就是「图和结构是两条平行路」的**形式原因**。** -/
theorem carrierGraph_not_medChain {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ¬ (carrierGraph M).Adj XZY.vX XZY.vZ :=
  carrierGraph_no_X_Z M

/-- ⭐⭐ **`medChainG` **确实有** `X → Z` 边**（与上条对撞，说明二者不是同一个图）。 -/
theorem medChainG_has_X_Z : medChainG.Adj XZY.vX XZY.vZ := trivial

/-- ⚠⚠ **第 285 轮更正（必读）**：下面这条**原名** `carrierGraph_differs_from_medChain`
的陈述 `∃ a b, Adj_carrier a b ∨ Adj_medChain a b` **是同义反复** ——
它**根本没提到**「两张图不同」：任取 `a = X, b = Z`，`medChainG.Adj X Z` 恒真，
故该命题**对任何 `carrierAdj` 都成立**（把 `carrierAdj` 换成恒 `True` 也成立）。
**⟹ 第 284 轮把它列为「⭐⭐ 判决：两者不是同一张图」是** overstated**。**
真实的「两图不同」是下面的 `carrierGraph_true_differs_from_medChain`。

本条**保留原名不改**（`SigCheck.lean` 已 `#check`），但**降级为「弱陈述」**。 -/
theorem carrierGraph_differs_from_medChain {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ∃ a b : XZY, (carrierGraph M).Adj a b ∨ medChainG.Adj a b :=
  ⟨XZY.vX, XZY.vZ, Or.inr medChainG_has_X_Z⟩

/-- ⭐⭐⭐⭐⭐ **真正**的「载体图 ≠ `medChainG`」（**第 285 轮新增**）。

$$\exists a\,b,\ \mathrm{Adj}_{\mathrm{medChain}}(a,b) \wedge \neg\,\mathrm{Adj}_{\mathrm{carrier}}(a,b)$$

**具体见证**：`a = X, b = Z` —— `medChainG` **有**这条边（`medChainG_has_X_Z`），
而**任何**模型的载体图**都没有**（`carrierGraph_no_X_Z`）。

**⭐⭐ 这是上面那条弱陈述的**实质版本**：它同时用到了 `carrierAdj` 与 `medChainAdj`，
故真的表达了「边集不同」。** -/
theorem carrierGraph_true_differs_from_medChain {Z X Y : Type} (M : R246G3.Sem3.SCM3 Z X Y) :
    ∃ a b : XZY, medChainG.Adj a b ∧ ¬ (carrierGraph M).Adj a b :=
  ⟨XZY.vX, XZY.vZ, medChainG_has_X_Z, carrierGraph_no_X_Z M⟩

end Bridge

/-! ### 8.3 ⭐⭐⭐⭐ **d-分离**不足以**刻画 `MediationInvariant`（反向见证）

**`medChain_dsep_rule2` 说**：在 `medChainG` 的 `rule2Graph` 上 `Z ⊥_d Y | X`。
**若这是桥，则它应推出 `MediationInvariant`。**
**下面证明**这不可能**：**构造一个模型**，它的方程**读 `X`**（`¬ MediationInvariant`），
**而 `medChainG` / `rule2Graph` 完全不变** —— **故任何只依赖该图的条件
都不足以排除它**。** -/

namespace Bridge

open R246G3

/-- ⭐⭐ **一个**违反** `MediationInvariant` 的模型**（`Y` 的方程 `fun p => p.2`，读 `x`）。 -/
noncomputable def readX : R246G3.Sem3.SCM3 (Fin 2) (Fin 2) (Fin 2) where
  U := Fin 2
  pU := fun _ => (1 : ℝ) / 2
  sg := fun u => ((u, u), fun p => p.2)

/-- ⭐⭐⭐ **`readX` **违反** `MediationInvariant`**（**前提真的能被打破**）。 -/
theorem readX_not_invariant : ¬ Sem.MediationInvariant readX := by
  intro h
  have hh : (readX.sg (0 : Fin 2)).2 ((0 : Fin 2), (0 : Fin 2))
      = (readX.sg (0 : Fin 2)).2 ((0 : Fin 2), (1 : Fin 2)) :=
    h (0 : Fin 2) ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) rfl
  exact absurd hh (by decide)

/-- ⚠⚠ **第 285 轮更正（必读）**：下面这条的陈述是
`Invariant chain ∧ ¬ Invariant readX` —— **它完全不含图 / d-分离**。
它**只是一个 `And.intro`**（`⟨chain_invariant, readX_not_invariant⟩`），
**拆开就能证**，与 `medChain_dsep_rule2` **无关**。

**⟹ 第 284 轮把它称为「⭐⭐⭐⭐⭐ 无桥的机器见证」（「d-分离推不出结构」的证明）
是** overstated**：它**没有把图侧条件放进来**，故不能说明图侧扮演什么角色。
真正的形式是下面的 `dsep_cannot_decide_invariant`（三项并列）。**

本条**保留原名不改**（`SigCheck.lean` 已 `#check`），但**降级为「两模型见证」**。 -/
theorem graph_cannot_decide_invariant :
    Sem.MediationInvariant R246G3.chain ∧ ¬ Sem.MediationInvariant readX :=
  ⟨Sem.chain_invariant, readX_not_invariant⟩

/-- ⭐⭐⭐⭐⭐ **真正**的「图侧无信息」定理（**第 285 轮新增**）。

$$\underbrace{\Bigl(Z \perp\!\!\!\perp_d Y \,\big|\, X\Bigr)_{G_{\underline X \bar Z}}}_{\text{图侧条件}}
  \;\wedge\;
  \textbf{MediationInvariant}(\mathrm{chain})
  \;\wedge\;
  \neg\,\textbf{MediationInvariant}(\mathrm{readX})$$

**⭐⭐ 为什么这条才是真见证**：`medChain_dsep_rule2` 的陈述里**没有任何模型变量**
（`medChainG` 是固定图），故**同一个**图侧条件**同时**与两个**相反**的结构判定成立。
**⟹ 图侧条件对结构条件**无分辨力** —— 这才是「`rule2Graph` 不能进主定理」的形式根据。**

**⚠ 与上面那条的差别**：上面那条**丢掉了**图侧条件（只留两个结构判定）；
本条把**图侧条件、正例、反例三者并列**，才真的表达了「图侧无信息」这一事实。
**（两者都**不能**推出「无条件不存在」——那只在换载体后才能谈，见 §7.3。）** -/
theorem dsep_cannot_decide_invariant :
    CausalDescendant.DSeparatedStd
        (DoCalculusRules.rule2Graph medChainG setX setZ) setX XZY.vZ XZY.vY
      ∧ Sem.MediationInvariant R246G3.chain
      ∧ ¬ Sem.MediationInvariant readX :=
  ⟨GraphCheck.medChain_dsep_rule2, Sem.chain_invariant, readX_not_invariant⟩

/-- ⭐⭐⭐⭐ **`readX` 的载体图**上的 `X → Y` 边**存在**（与 `chain` 相反），
**而这正是载体图**唯一**能反映结构差别的边。

**⚠ 但注意**：这**不是**桥 —— 它就是 `ReadsX` 的定义展开（`invariant_iff_no_X_Y`）。** -/
theorem readX_carrier_X_Y : (carrierGraph readX).Adj XZY.vX XZY.vY :=
  ⟨(0 : Fin 2), ((0 : Fin 2), (0 : Fin 2)), ((0 : Fin 2), (1 : Fin 2)), rfl, by decide⟩

/-- ⭐⭐ **`chain` 的载体图上**没有** `X → Y` 边**（它满足不变量）。 -/
theorem chain_carrier_no_X_Y : ¬ (carrierGraph R246G3.chain).Adj XZY.vX XZY.vY :=
  (Bridge.invariant_iff_no_X_Y R246G3.chain).mp Sem.chain_invariant

end Bridge

/-! ### 8.4 ⭐⭐⭐⭐⭐ **判决**

#### ① 直接回答任务书的问题

> **为什么主定理没用图条件？**

**因为它**不可能**用 —— 不是「缺一个桥」，是**结构上不存在桥**：

| 层 | 内容 | 图 |
|---|---|---|
| **载体** `Sem3.SCM3 Z X Y` | **一条**方程 `f_u : Z × X → Y` | `carrierGraph M`：`Z → Y` 恒有，`X → Y` 视方程 |
| **本题的图** `medChainG` | 「`Z` 是 `X` 的**中介**」 | `X → Z`、`Z → Y` |

**⚠⚠ `medChainG` **有** `X → Z` 边（`medChainG_has_X_Z`），
而**载体图**对**任何模型**都**没有**这条边（`carrierGraph_no_X_Z`）。**

**⟹ `medChainG` 不是任何模型的图**（`carrierGraph_true_differs_from_medChain`，**第 285 轮修正版**；
旧名 `carrierGraph_differs_from_medChain` 是同义反复的弱陈述，已标注）。
**⟹ §6 的 `medChain_dsep_rule2` 说的是一个**载体里不存在的图**上的性质。**

**⚠⚠ 第 285 轮更正**：下面这句是第 284 轮的** overstated** 说法。真实情况：
对于**载体自身**的图（`carrierGraph M`），`MediationInvariant` 确实**与「`X → Y` 无边」等价**
（`invariant_iff_no_X_Y`）—— **但这只是因为 `X → Y` 边的判据被定义为 `ReadsX`（即 `¬Invariant`）**。
故对载体图而言，d-分离→结构的**推导是**同义反复**，不是**真桥**。
**对载体图外的图 `medChainG`，真正的无信息见证**是 `dsep_cannot_decide_invariant`
（图侧条件与两个**相反**的结构判定同时成立）——**第 285 轮新增**。

#### ② 是「缺桥」还是「结构性质不需要图」？

**都不是** —— 更准确：

- **结构性质本身**（`MediationInvariant` = 「`f_u` 不读第二分量」）
  **不需要图**：它是**方程**的性质，`exists_medFactor_of_invariant` 直接把它翻译成 `g_u(z)`。
  **图**在**这个载体上**没有额外信息可给 —— **因为载体只有一条方程**。
- **`rule2Graph` **不是桥的候选**，而是**另一个载体的图**（Pearl 的 `X → Z → Y` 三方程模型）。

#### ③ `rule2Graph` 是装饰吗？

**⚠ 在本文件里，是。** 精确地说：

| 断言 | 判定 |
|---|---|
| `rule2Graph` **定义**正确（`delIn (delOut G VZ) VX`）| ✅ |
| `medChainG` 上 `Z ⊥_d Y \| X` **在 `rule2Graph medChainG` 上成立** | ✅ **§6 真定理** |
| 该 d-分离 **推出** `MediationInvariant` | ❌ **§8.3 `dsep_cannot_decide_invariant`**（第 285 轮：图侧与两个相反判定并列）|
| `rule2_genuine` 的证明链**可以**消费 `rule2Graph` | ❌ **不可能**（图不属于该载体）|

**⟹ `rule2Graph` **对它自己的载体**（Pearl 三方程模型）是**实质的**；
**对 `Sem3.SCM3` **是装饰**。**
**⟹ 要让 `rule2Graph` 真的进入主定理，必须先换载体（§7.3 的 `SCM3'`），
**使 `Z` 有**自己的方程** `fZ : Uz → Z`，从而使 `X → Z` 边**存在**。**

**⚠⚠ 第 285 轮：换载体也**不自动**接上图（已实测）**。构造三方程载体
```lean
structure SCM3' (Z X Y : Type) where
  Ux Uz Uy : Type; pUx pUz pUy : ℝ → ...
  fX : Ux → X; fZ : X → Uz → Z; fY : Z → Uy → Y
```
并把其忠实图 `fidG M` 的 `X → Y` 边判据设为恒 `False`（因为 `fY` 的**签名里没有 `x` 位`），
则得到 `fidG_no_X_Y : ¬(fidG M).Adj X Y` **对任何 `M` 都成立**，
**不依赖任何假设**。**⟹ 换载体「解决」缺口 3 的方式是**把条件变恒真**
（「`Y` 不读 `x`」成为**签名假设**），**而不是把条件变成图上的 d-分离。**
**⟹ 这是**把条件删掉**，不是桥。**（实测代码：`_probe_r285_scm3p.lean`，不入库。）

#### ④ 本节的**净产出**（诚实清单）

| # | 结果 | 值 |
|---|---|---|
| 1 | `invariant_iff_not_readsX` | 换写（`ReadsX` = `¬Invariant`）|
| 2 | `carrierGraph`（DAG，`carrierAdj_acyclic`）| 新对象（**但只对载体忠实**）|
| 3 | `invariant_iff_no_X_Y` | **定义展开**（⚠ 不是桥）|
| 4 | `carrierGraph_no_X_Z` | ⭐ **真事实**：载体无 `Z` 方程 ⟹ 无 `X → Z` |
| 5 | `medChainG_has_X_Z` | ⭐ **真事实**：`medChainG` 有 `X → Z` |
| 6 | `carrierGraph_differs_from_medChain` | ⚠ **弱陈述**（`∨` 形式，与 `carrierAdj` 无关）——第 285 轮降级 |
| 6′ | `carrierGraph_true_differs_from_medChain` | ⭐⭐⭐ **真判决**：`∃ a b, Adj_medChain a b ∧ ¬Adj_carrier a b`（第 285 轮新增）|
| 7 | `readX_not_invariant` | ⭐⭐ **前提可被打破**（非恒真）|
| 8 | `graph_cannot_decide_invariant` | ⚠ **两模型见证**（不含图）——第 285 轮降级 |
| 8′ | `dsep_cannot_decide_invariant` | ⭐⭐⭐⭐ **真「图侧无信息」**：图侧条件 + 正例 + 反例三者并列（第 285 轮新增）|

**⚠⚠ 第 285 轮的更正（必读）**：第 284 轮把 #6 与 #8 升为「判决 / 无桥的机器见证」，
**二者都** overstated**：
- #6 的陈述是 `∃ a b, Adj_carrier a b ∨ Adj_medChain a b`，**任取 `X,Z` 右侧恒真**，
  故此命题**对任何 `carrierAdj` 都成立**（换成恒 `True` 也成立）—— **它不是「两张图不同」**。
- #8 的陈述 `Invariant chain ∧ ¬ Invariant readX` **完全不含图 / d-分离**，
  只是一个 `And.intro` —— **它没把图侧条件放进来**，故不能说明图侧无信息。

**⟹ 正确的说法是 #6′ 与 #8′。 结论方向（图侧接不进主定理）仍成立，
但第 284 轮给的**证据本身**不够力。**

**⟹ 本节的**真负结论**（方向不变，依据修正）：
1. **载体层**：载体无 `Z` 方程 ⟹ 无 `X → Z` 边（`carrierGraph_no_X_Z`），
   而 `medChainG` 有（`medChainG_has_X_Z`），故载体图 ≠ `medChainG`（**#6′**）；
2. **图侧无信息**：`rule2Graph` 上的 d-分离对它自己的图**与模型无关**，
   与两个**相反**的结构判定同时成立（**#8′**）；
3. **变载体也不行**：三方程载体让「`Y` 不读 `x`」变**定义**（实测），不是桥；
4. **真正缺的两步仍未做**：`dSep ⟹ 条件独立`（缺口 1，见 `GlobalMarkovChain4` 6.2）
   与「条件独立 ⟹ 规则 2 定律」。**这两端都断，故图侧链条在这个仓库里完全不能闭合。**

**⟹ `rule2Graph` 对 `Sem3.SCM3` 是**装饰**（已标注，不改名不删）；
它只作为 Pearl 三方程模型的图有独立价值。** -/

/-! ===========================================================================
  §R42  规则 2 的「交换」方向：方案树上的最优值（消费 `InterventionSup`）

  ## 为什么放在这里

  `Fate/InterventionSup.lean` 用 `Finset.sup'` 定义最优值 `bestScoreSup`，
  并证了四条**真紧性**（上界 / 取等 / 最小上界 / 锐利性），
  但此前 **零外部引用**（R-42）。

  规则 2 的实质是「**交换** `X = x` 与 `Z = z` 两个动作的顺序」。
  交换后的**候选顺序集合**是一个有限对象；在它上面「选哪个顺序最好」
  正是 `InterventionSup.bestScoreSup` 的用武之地。

  本节**只**做组合层桥接，**不**声称规则 2 成立。

  ## 防环检查（第 237 条）

  * 本节前：`grep -c "^import FateV2.Predict.InterventionSup$" Fate/Rule2Genuine.lean` = 0
  * `InterventionSup` 及其全部上游（`InterventionTight` → `PolicyAlgorithm`、
    `InterventionSelection` → `Frame`）中**不出现** `Rule2Genuine`：
    `grep -E "Rule2Genuine" Fate/InterventionSup.lean Fate/InterventionTight.lean
     Fate/PolicyAlgorithm.lean Fate/InterventionSelection.lean` 为空。
  * 故在本文件消费 `InterventionSup` **不成环**。

  ## 诚实边界

  1. 本节的「最优」相对于**参数** `P.score`；本文件**不**填 `score`。
  2. 本节**不**断言交换律、**不**断言任何 SCM 的识别结论。
  3. 论域是有限树（`Finset`），与 `InterventionSup` 一致。
  4. 零 `sorry` / 零 `axiom` / 零 `native_decide`。
-/

namespace Rule2SupConsume

open FateV2.Predict.WorldScenario
open FateV2.Predict.WorldScenario.InterventionSup

universe u

/-- ⭐⭐⭐ **【真实消费者】交换方案树上的得分上界**

`InterventionSup` 的首条主定理：树中任一方案不超过最优值。 -/
theorem exchange_score_le_sup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (s : Scenario A X) (hs : s ∈ tree) :
    P.score s ≤ FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne :=
  FateV2.Predict.WorldScenario.InterventionSup.le_bestScoreSup P tree hne s hs

/-- ⭐⭐⭐⭐ **【真实消费者】最优交换顺序存在**

消费 `Fate.WorldScenario.InterventionSup.bestScoreSup_mem_image`（真紧性）。 -/
theorem exists_exchange_order_attains_sup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne := by
  obtain ⟨s, hs, hEq⟩ := FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_mem_image P tree hne
  exact ⟨s, by simpa using hs, hEq⟩

/-- ⭐⭐⭐ **【真实消费者】交换方案树的阈值判据**

消费 `Fate.WorldScenario.InterventionSup.bestScoreSup_isLUB`：验证 `beta` 是安全阈值
等价于验证最优值不超过 `beta`，**无需遍历树**。 -/
theorem exchange_threshold_iff {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (beta : ℝ) :
    (∀ s ∈ tree, P.score s ≤ beta) ↔
      FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne ≤ beta :=
  FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_isLUB P tree hne beta

/-- ⭐⭐⭐ **【真实消费者】最优交换顺序的锐利性**

消费 `Fate.WorldScenario.InterventionSup.bestScoreSup_sharp`：任一下调都失效。 -/
theorem exchange_sup_sharp {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ s ∈ tree, FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne - eps < P.score s :=
  FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup_sharp P tree hne heps

/-- ⭐⭐⭐⭐ **【主结论】最优交换顺序存在且最优（合取形式）**

消费 `bestScoreSup_mem_image` 与 `le_bestScoreSup`。 -/
theorem exchange_exists_max {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = FateV2.Predict.WorldScenario.InterventionSup.bestScoreSup P tree hne ∧
      ∀ t ∈ tree, P.score t ≤ P.score s := by
  obtain ⟨s, hs, hEq⟩ := exists_exchange_order_attains_sup P tree hne
  refine ⟨s, hs, hEq, ?_⟩
  intro t ht
  rw [hEq]
  exact exchange_score_le_sup P tree hne t ht

end Rule2SupConsume

end R248

end FateV2.Predict