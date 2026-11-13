import FateWorld.FateV2.Predict.CausalDirection

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CausalPath.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 5 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! ===========================================================================
  §62  **d-分离的**路径层****：逐节点开口性

  ## 背景

  | 轮次 | 已做 |
  |---|---|
  | **60** | 图论层（路径、顶点集、阻断）|
  | **61** | 方向层（三元组四类、collider 判据）|

  **⚠ 第 61 轮的边界登记**：
  > **本节只形式化**单个三元组的方向分类**；
  > **「整条路径的 d-连通」需要逐节点的开口性归纳**

  **⟹ 本轮补上这一层 —— d-分离的**纯图论部分**到此完整。**

  ## ⚠ 设计困难与解法

  **困难**：**`SimpleGraph.Walk` 是**无向**的**（只有 `Adj`），
  而 d-分离需要知道**路径上每条边的方向**。

  **⟹ 解法**：**把方向存为**路径上的附加数据**** ——
  **即「带向路径」（`DWalk`）：顶点序列 + 每步的方向标记。**

  ## 本节的产出

  | # | 内容 |
  |---|---|
  | **1** | **`DStep`**：带向的一步（`fwd` / `bwd`）|
  | **2** | **`DWalk`**：带向路径（顶点 + 步骤序列）|
  | **3** | **`openAt`**：**单个中间点的开口性**（**d-分离的核心判据**）|
  | **4** | **`DOpen`**：**整条路径开口** |
  | **5** | **`DConnected`**：**d-连通**（存在开口路径）|

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict

namespace CausalPath

universe u

variable {V : Type u}

/-! ### §62.1 带向路径 -/

/-- **带向的一步**：从当前顶点出发，指向 `next`。

**⚠ 与 `SimpleGraph.Walk` 的关键差别**：
**后者只有「相邻」，本节额外记录**方向**。** -/
inductive DStep (G : CausalDirection.CausalGraph V) : V → V → Type u where
  /-- **前向**：`from → to`。 -/
  | fwd {a b : V} (h : G.Adj a b) : DStep G a b
  /-- **后向**：`to → from`（即沿边逆向行进）。 -/
  | bwd {a b : V} (h : G.Adj b a) : DStep G a b

/-- **带向路径**：顶点序列 + 步骤序列。

$$\mathrm{DWalk}\,G\,a\,b :=
  a = v_0 \xrightarrow{s_1} v_1 \to \cdots \xrightarrow{s_n} v_n = b$$ -/
inductive DWalk (G : CausalDirection.CausalGraph V) : V → V → Type u where
  /-- **零步路径**。 -/
  | nil (a : V) : DWalk G a a
  /-- **扩展一步**。 -/
  | cons {a b c : V} (s : DStep G a b) (w : DWalk G b c) : DWalk G a c

/-! ### §62.2 开口性（d-分离的核心判据） -/

/-- **单个中间点的开口性**（**d-分离的核心判据**）。

$$\text{openAt}(s_1, s_2, b, Z) :=
  \begin{cases}
    b \in Z & \text{若 } b \text{ 是 collider}\ (s_1 = \mathrm{fwd} \wedge s_2 = \mathrm{bwd})\\
    b \notin Z & \text{否则}
  \end{cases}$$

**⟹ 这是 d-分离**唯一**「行为反转」之处**：
**中间点若是 collider，则**在 `Z` 中才开口**；
**否则**不在 `Z` 中才开口**。**

**⚠ 说明**：**严格的 d-分离还包括「collider 的**后代**在 `Z` 中也开口」；
**本节暂只做 collider 本身的情形**（见文件末的边界登记）。** -/
def openAt (G : CausalDirection.CausalGraph V) {a b c : V}
    (s₁ : DStep G a b) (s₂ : DStep G b c) (Z : Set V) : Prop :=
  match s₁, s₂ with
  | .fwd _, .bwd _ => b ∈ Z      -- collider：在 `Z` 中才开口
  | _, _ => b ∉ Z                -- 非 collider：不在 `Z` 中才开口

/-- **collider 判据（带向形式）**：`fwd` 接 `bwd`。 -/
theorem isCollider_of_fwd_bwd (G : CausalDirection.CausalGraph V) {a b c : V}
    {s₁ : DStep G a b} {s₂ : DStep G b c}
    (h₁ : ∃ h : G.Adj a b, s₁ = .fwd h) (h₂ : ∃ h : G.Adj c b, s₂ = .bwd h) :
    CausalDirection.IsCollider G a b c := by
  obtain ⟨ha, _⟩ := h₁
  obtain ⟨hb, _⟩ := h₂
  exact ⟨ha, hb⟩

/-! ### §62.3 整条路径的开口性 -/

/-- **整条路径开口**（所有中间点都开口）。

$$\mathrm{DOpen}(w, Z) := \text{每个中间点 } v_i \text{ 处 } \mathrm{openAt} \text{ 成立}$$

**⚠ 递归方式**：逐层剥去**第一步**，
并把「第一步与第二步」的开口性作为**并列合取**（而非嵌套）。 -/
def DOpen (G : CausalDirection.CausalGraph V) (Z : Set V) :
    {a b : V} → DWalk G a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons _ (.nil _) => True
  | _, _, .cons s₁ (.cons s₂ w) => openAt G s₁ s₂ Z ∧ DOpen G Z (.cons s₂ w)

/-- **d-连通**（**本节的核心定义**）。

$$a \text{ 与 } b \text{ 在 } Z \text{ 下 d-连通} :=
  \exists\, \text{开口的带向路径 } a \to b$$

**⟹ 即**：**「存在一条所有中间点都开口的路径」** ——
**这是 d-分离的**完整图论定义**（方向 + 开口性）。** -/
def DConnected (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  ∃ w : DWalk G a b, DOpen G Z w

/-- ⚠ **d-分离（**简化版**，**不是** Pearl 的标准定义）**。

$$a \perp\!\!\!\perp_{d}^{s} b \mid Z := \neg\,\mathrm{DConnected}\,G\,Z\,a\,b$$

**⚠ 本定义**漏掉了**「collider 的后代在 `Z` 中」这一条**：
`openAt` 的 collider 分支只判 `b ∈ Z`，而 Pearl 的标准定义是
「`b ∈ Z` **或 `b` 的某个后代 ∈ `Z`」**。

**⟹ 故本定义**比标准定义**弱**，会**误报分离** ——
**当一条路径只经「被条件化的后代」开口时，本定义判为分离，实际**不**分离。**

**标准定义见** `FateV2.Predict.CausalDescendant.DSeparated'`
（**用 `Reach`，与 Pearl《Causality》§1.2.3 定义 1.2.3 一致**）。

**⚠ 本定义**保留仅为**向下兼容**（`CausalDescendant.openAt_imp_openAt'` 依赖它）——
**新代码请用 `DSeparated'`。** -/
def DSeparated (G : CausalDirection.CausalGraph V) (Z : Set V) (a b : V) : Prop :=
  ¬ DConnected G Z a b

/-! ### §62.4 基本性质

**⚠ 第 230 轮的说明**：`DOpen` 由 `brecOn` 生成，`simp [DOpen]` 在
**三步以上**的路径上会因 `DWalk.rec` 的自动生成项而**超时，
故 `FateV2.Predict.CausalOpen` 只用 `DOpen'`（结构递归，无此问题）。
**本节的 `dopenn_nil` / `dopenn_single` 只在 `nil` / 单边路径上展开，无碍。** -/

/-- **零步路径总是开口**（平凡情形）。 -/
theorem dopenn_nil (G : CausalDirection.CausalGraph V) (Z : Set V) (a : V) :
    DOpen G Z (DWalk.nil (G := G) a) :=
  trivial

/-- **单边路径总是开口**（无中间点）。 -/
theorem dopenn_single (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (s : DStep G a b) : DOpen G Z (DWalk.cons s (DWalk.nil b)) :=
  trivial

/-- **d-连通的自反性**（**基本定理**）。

$$a \text{ 与 } a \text{ 总在任意 } Z \text{ 下 d-连通}$$

**⟹ 即**：**零步路径总是开口** ——
**这是 d-连通关系的最基本性质。** -/
theorem dconnected_refl (G : CausalDirection.CausalGraph V) (Z : Set V) (a : V) :
    DConnected G Z a a :=
  ⟨DWalk.nil a, trivial⟩



/-- **d-分离的不可自反性**（**重要推论**）。

$$\neg\,(a \perp\!\!\!_d a \mid Z)$$

**⟹ 即**：**任何点都不与自己 d-分离** ——
**这是「d-分离」作为**独立性**关系的必要性质**
（独立关系通常要求 $a \not\perp a$）。** -/
theorem not_dseparated_self (G : CausalDirection.CausalGraph V) (Z : Set V) (a : V) :
    ¬ DSeparated G Z a a :=
  fun h => h (dconnected_refl G Z a)

end CausalPath

end FateV2.Predict
