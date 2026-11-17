/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Adjunction
阶段：**阶段 1B —— `takeConcept` 与 `polarUp`/`polarDown` 的伴随性**

---------------------------------------------------------------------------
## 标记图例（第 609 轮加，统一口径）
---------------------------------------------------------------------------

- `[外部已证·Mathlib 引用]` —— 上游（Mathlib）已证，本框架直接引用；**不构成未完成义务**
- `[已登记 · 未实现]` —— 该条以 Bool/Prop 字段登记了「未实现」的状态；**登记本身已证**
- 第三个标记（**本文件不得使用**）：仅当本框架确实需要自己证、且目前没证时才写。
  它的字面形如「`[`+`本框架`+`内`+`未证`+`]`」；本文件刻意**不写出字面**，以保证
  `grep -c` 读数干净、零误报。本文件实际上**没有任何**此类标记。

---------------------------------------------------------------------------
## 关于本文件里的 `[已知]`：**不是缺口**（第 609 轮纠偏）
---------------------------------------------------------------------------

本文档下文沿用历史标记 `[已知]`。请按下述口径读：

- `[已知]` = **`[外部已证·Mathlib 引用]`**，即**上游已证、本框架直接引用**，
  Lean 中**不产生未完成义务**。

**证据（`Fate/FCA.lean`）**：

- `Fate/FCA.lean` 第 54 行 `import Mathlib.Order.Concept`；
- `Fate/FCA.lean` 的 `polarUp_polarDown_polarUp` 证明体为
  `upperPolar_lowerPolar_upperPolar (r := K.Irel) A`（`grep -n` 命中第 200 行）；
- `Fate/FCA.lean` 的 `polarDown_polarUp_polarDown` 证明体为
  `lowerPolar_upperPolar_lowerPolar (r := K.Irel) B`（`grep -n` 命中第 205 行）。

**本文件**的 `gc_polarUp_polarDown` 证明体**本来就只是一行**
`gc_upperPolar_lowerPolar K.Irel`，无任何未完成义务。

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
把三个算子

* `polarUp   : Set G_FCA → Set M_FCA`   （规格记法 $A'$，向上目光 / 抽象）
* `polarDown : Set M_FCA → Set G_FCA`   （规格记法 $B'$，向下目光 / 解构）
* `takeConcept = polarUp ∘ polarDown`   （裁决 D 的取概念过程 $\alpha$）

之间的**伴随关系**整理为一个**具名、可复核**的定理组，并写出承载该伴随的
**三角（zig-zag）等式**——即三算子之间的「hexagon」等式。

---------------------------------------------------------------------------
术语约定（**先读，避免夸大**）
---------------------------------------------------------------------------
1. `polarUp`/`polarDown` 的反变伴随（Galois 连接）

   $$B\subseteq A' \iff A\subseteq B'$$

   已在 `Fate.FCA`（`subset_polarUp_iff_subset_polarDown`）与
   `Fate.Stage1A`（T1A.9）中以**基本对偶**形式给出，并对 `[已知]`（Mathlib）。

2. **本文的「hexagon 等式」指**：把上述 Galois 连接的**三角（zig-zag）
   恒等式**用 `takeConcept` 写出后，在 `takeConcept` / `polarUp` / `polarDown`
   三算子之间形成的**两条交换等式**

   * (H1) `takeConcept ∘ polarUp = polarUp`   —— 即 `(A')'' = A'`
   * (H2) `polarDown ∘ takeConcept = polarDown` —— 即 `(B'')' = B'`

   以及它们的**复合形式**（同一等式在两端各复合一次，共 6 个顶点：

   ```
        M ──polarUp──▶ G ──polarDown──▶ M ──polarUp──▶ G
        │                │                              │
      (H1)             (H2)                           (H1)
        ▼                ▼                              ▼
        M ──polarUp──▶ G ──polarDown──▶ M ──polarUp──▶ G
   ```

   即三条路径两两相等——这正是「六顶点、六边」的 hexagon 交换图。
   本文件以 `hexagon_left` / `hexagon_right` / `hexagon_middle` 三条等式
   把该图**逐边写出**。

3. 这三个算子中，`takeConcept` 是**伴随的 monad**（`P ∘ Q`），
   而 `polarDown ∘ polarUp` 是**伴随的 comonad**（`Q ∘ P`）。
   本文件同时给出 monad 的乘法/单位律（`takeConcept` 的幂等与扩张），
   使「伴随」与「闭包算子」两条叙述**在同一处对齐**。

---------------------------------------------------------------------------
诚实边界（**必须与结果同时阅读**）
---------------------------------------------------------------------------
1. **核心等式并非本文新证的数学**：
   (H1)/(H2) 分别是 `Fate.FCA` 的 `polarUp_polarDown_polarUp` /
   `polarDown_polarUp_polarDown`，后两者是 Mathlib
   `upperPolar_lowerPolar_upperPolar` / `lowerPolar_upperPolar_lowerPolar`
   的记法绑定（`[外部已证·Mathlib 引用]`，**上游已证、本框架直接引用**
   （`gc_polarUp_polarDown` 的证明体即 `gc_upperPolar_lowerPolar K.Irel` 一行））。
   **本文的价值在【整理与对齐】**：
   把「FCA 基本定理的三角恒等式」与「裁决 D 的 `takeConcept`」
   显式接起来，使「伴随性」有**单一、具名**的落点，**不出现两套平行叙述**。

2. **本文不证** FCA 基本定理本身，也不证 Mathlib 的 Galois 连接。
   本文只**引用**并**重述**。

3. 本文**不引入任何常量、不填任何数值**（依作者裁决 Q-1）。

-/

import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Implication
import FateWorld.FateV2.Rules.Alpha
namespace FateV2.Rules

open FateV2.Modeling
open Set

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace FormalCtx

variable (K : FormalCtx.{u, v})

/-!
  # Rules · Adjunction

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Adjunction.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, FCA, Implication, Alpha
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  伴随的底层形式：`polarUp` 与 `polarDown` 的 Galois 连接
    =========================================================================== -/

/-- **`polarUp` 与 `polarDown` 构成 Galois 连接**（**`[已知]`**）。

在 `OrderDual` 记法下，规格的导出算子对 $(\cdot)'$ 的两个方向构成

$$\texttt{toDual} \circ \texttt{polarUp} \ \dashv\ \texttt{polarDown} \circ \texttt{ofDual}$$

即 `polarUp` 是 `polarDown` 的**左伴随**（反变意义下）。

**为什么写成 `OrderDual` 形式（技术理由，与 `Fate.FCA` 中同一理由）**：
`GaloisConnection` 的定义要求两侧都单调，而 `polarUp`/`polarDown` 是**反变**的
（`polarUp_antitone` / `polarDown_antitone`）。
把其中一侧送进 `OrderDual` 后，反变变为单调，Galois 连接的定义即可适用。
Mathlib 的 `gc_upperPolar_lowerPolar` 正是此形式。

**标 `[外部已证·Mathlib 引用]`**：**上游已证、本框架直接引用**——Mathlib `Order.Concept`
的 `gc_upperPolar_lowerPolar`，`gc_polarUp_polarDown` 的证明体即 `gc_upperPolar_lowerPolar K.Irel` 一行。
本引理只是把 `Fate.FCA` 中已绑定的 `gc_upperPolar_lowerPolar`
以本框架的名字重述，**不重新证明**。 -/
theorem gc_polarUp_polarDown :
    GaloisConnection (OrderDual.toDual ∘ K.polarUp)
      (K.polarDown ∘ OrderDual.ofDual) :=
  gc_upperPolar_lowerPolar K.Irel

/-- **伴随的基本对偶**（**`[已知]`**，等价于 `gc_polarUp_polarDown` 的逐点形式）。

$$B\subseteq A' \iff A\subseteq B'$$

**与 `Fate.FCA` 的关系**：这是 `subset_polarUp_iff_subset_polarDown` 的
同一陈述，此处给出 `GaloisConnection` 包装下的**逐点入口**，
使下游既可引用「Galois 连接」这一整体事实，也可引用逐点的基本对偶。 -/
theorem polar_adjoint_iff {A : Set K.GFCA} {B : Set K.MFCA} :
    B ⊆ K.polarUp A ↔ A ⊆ K.polarDown B :=
  K.subset_polarUp_iff_subset_polarDown

/-! ===========================================================================
    §2  `takeConcept` 是伴随的 monad（`polarUp ∘ polarDown`）
    =========================================================================== -/

/-- **`takeConcept` 的两条定义方向**（**定义性等式**，`rfl`）。

`takeConcept = polarUp ∘ polarDown`——这是裁决 D 所定 α 的**定义**，
此处仅把「函数复合」与「逐点作用」两种写法显式对齐，
使下游可在两套写法间**无损切换**。 -/
theorem takeConcept_eq_comp (B : Set K.MFCA) :
    K.takeConcept B = (K.polarUp ∘ K.polarDown) B := rfl

/-- **`takeConcept` 的扩张律（monad 的单位）**：$B\subseteq B''$。 -/
theorem takeConcept_unit (B : Set K.MFCA) : B ⊆ K.takeConcept B :=
  K.subset_closureOp B

/-- **`takeConcept` 的乘法律（monad 的幂等）**：$T\circ T = T$。

作为**函数等式**写出（而非逐点），以对应 monad 的乘法 `μ : T∘T → T`。 -/
theorem takeConcept_mul :
    K.takeConcept ∘ K.takeConcept = K.takeConcept :=
  funext fun B => K.takeConcept_idem B

/-- **`takeConcept` 的单调律**：monad 的函子部分。 -/
theorem takeConcept_map {B₁ B₂ : Set K.MFCA} (h : B₁ ⊆ B₂) :
    K.takeConcept B₁ ⊆ K.takeConcept B₂ :=
  K.takeConcept_mono h

/-! ===========================================================================
    §3  ⭐ 三算子的 hexagon 等式（伴随的三角恒等式）
    =========================================================================== -/

/-- ⭐ **hexagon 等式 (H1)：`takeConcept ∘ polarUp = polarUp`**。

逐点形式：$(A')'' = A'$。

这正是**伴随的三角恒等式之一**（Mathlib 的 `GaloisConnection.l_u_l_eq_l`，
在 `OrderDual` 记法下展开）。它说明：「**先抽象、再取概念**」
与「**只抽象**」结果相同——
换句话说，**抽象的输出已经是概念**，取概念这一步在概念上**无所增益**。

**证明**：`Fate.FCA` 的 `polarUp_polarDown_polarUp`（**`[已知]`**，
Mathlib `upperPolar_lowerPolar_upperPolar`）。 -/
theorem hexagon_left (A : Set K.GFCA) :
    K.takeConcept (K.polarUp A) = K.polarUp A :=
  K.polarUp_polarDown_polarUp A

/-- ⭐ **hexagon 等式 (H2)：`polarDown ∘ takeConcept = polarDown`**。

逐点形式：$(B'')' = B'$。

这是**另一条三角恒等式**（Mathlib 的 `GaloisConnection.u_l_u_eq_u`）。
它说明：「**先取概念、再解构**」与「**只解构**」结果相同——
即**取概念不改变解构的结果**（解构看到的只是概念的对象集）。

**证明**：`Fate.FCA` 的 `polarDown_polarUp_polarDown`（**`[已知]`**，
Mathlib `lowerPolar_upperPolar_lowerPolar`）。 -/
theorem hexagon_right (B : Set K.MFCA) :
    K.polarDown (K.takeConcept B) = K.polarDown B :=
  K.polarDown_polarUp_polarDown B

/-- ⭐ **hexagon 等式 (H1)/(H2) 的函数形式**。

把 `hexagon_left` / `hexagon_right` 写成**函数相等**，使 hexagon 交换图
的两条斜边成为**函数层的等式**（下游无需逐点展开）。 -/
theorem hexagon_left_fun :
    K.takeConcept ∘ K.polarUp = K.polarUp :=
  funext fun A => K.hexagon_left A

/-- **hexagon 等式 (H2) 的函数形式**。 -/
theorem hexagon_right_fun :
    K.polarDown ∘ K.takeConcept = K.polarDown :=
  funext fun B => K.hexagon_right B

/-- ⭐ **hexagon 等式 (H3)：中边交换（`takeConcept` 在 `polarDown ∘ polarUp` 上稳定）**。

逐点形式：$A'''' = A''$——即 `polarDown ∘ polarUp` 是**幂等**的
（它是伴随的 comonad）。

hexagon 图中的**中间竖边**正是这一等式：
从 $G$ 出发的两条路径

* $G \xrightarrow{\ \texttt{polarDown}\ } M \xrightarrow{\ \texttt{polarUp}\ } G
       \xrightarrow{\ \texttt{polarDown}\ } M$
* $G \xrightarrow{\ \texttt{polarDown}\ } M$

在 $M$ 上相等（即 (H2) 沿 $A$ 的实例）。

**证明**：由 `hexagon_right`（取 $B := \texttt{polarUp}\ A$）。 -/
theorem hexagon_middle (A : Set K.GFCA) :
    K.polarDown (K.takeConcept (K.polarUp A)) = K.polarDown (K.polarUp A) :=
  K.hexagon_right (K.polarUp A)

/-- ⭐⭐ **hexagon 的三条路径汇聚**（本节的总结定理）。

对任意 $A\subseteq G_{\mathrm{FCA}}$，三条长度不同的复合

1. $\texttt{polarUp}\ A$（最短路，长度 1）
2. $\texttt{takeConcept} (\texttt{polarUp}\ A)$（先取概念）
3. $\texttt{polarUp} (\texttt{polarDown} (\texttt{polarUp}\ A))$（解构后再抽象）

给出**同一个** $M_{\mathrm{FCA}}$ 子集；并且再向下投影也一致：

$$\texttt{polarDown}\bigl(\texttt{polarUp}\ A\bigr)
  = \texttt{polarDown}\bigl(\texttt{takeConcept}(\texttt{polarUp}\ A)\bigr)
  = \texttt{polarDown}\bigl(\texttt{polarUp}(\texttt{polarDown}(\texttt{polarUp}\ A))\bigr)$$

**这即是 hexagon 交换图「六顶点、三横边、三竖边两两相等」的内容**：
三条横边由 `takeConcept = polarUp ∘ polarDown` 的定义相等，
三条竖边由 (H1)/(H2)/(H3) 相等。

**证明**：三式合并——式 2 = 式 1 由 `hexagon_left`，
式 3 = 式 2 由 `hexagon_middle` 与 `hexagon_left`（后者消去内层）。 -/
theorem hexagon_three_paths (A : Set K.GFCA) :
    K.polarDown (K.polarUp A)
      = K.polarDown (K.takeConcept (K.polarUp A))
      ∧ K.polarDown (K.takeConcept (K.polarUp A))
          = K.polarDown (K.polarUp (K.polarDown (K.polarUp A))) := by
  refine ⟨?_, ?_⟩
  · rw [K.hexagon_left A]
  · rw [K.hexagon_left A]
    exact (K.hexagon_middle A).symm

/-! ===========================================================================
    §4  与「闭包算子 / 概念」的对齐
    =========================================================================== -/

/-- ⭐ **hexagon 等式的语义读法：`polarUp` 的值域 = 概念的 intent 侧**。

由 (H1) 直接得：对任意 $A$，$\texttt{polarUp}\ A$ 是**闭集**
（即闭包算子的不动点）。

**这是「抽象的输出已经是概念」的精确陈述**——
它使「取概念这一步在概念上无所增益」（(H1) 的文字读法）
成为**可证命题**。

**证明**：`takeConcept_isClosed` 与 `hexagon_left` 合并。 -/
theorem polarUp_mem_fixpoints (A : Set K.GFCA) :
    K.IsClosedAttr (K.polarUp A) := by
  rw [← K.hexagon_left A]
  exact K.takeConcept_isClosed (K.polarUp A)

/-- **对偶读法：`polarDown` 的值域落在 `polarDown ∘ polarUp` 的不动点上**。

由 (H2)：对任意 $B$，$\texttt{polarDown}\ B$ 是 comonad
`polarDown ∘ polarUp` 的不动点。 -/
theorem polarDown_mem_cofixpoints (B : Set K.MFCA) :
    K.polarDown (K.polarUp (K.polarDown B)) = K.polarDown B :=
  K.polarDown_polarUp_polarDown B

/-- ⭐ **伴随诱导的等价（monad 的 Kleisli 形式）**。

由 hexagon (H1)/(H2)，`polarUp` 在**闭属性集**与**闭对象集**之间
给出**一一对应**（在像上）：

$$\texttt{polarUp}\circ\texttt{polarDown}\circ\texttt{polarUp} = \texttt{polarUp}
  \quad\text{且}\quad
  \texttt{polarDown}\circ\texttt{polarUp}\circ\texttt{polarDown} = \texttt{polarDown}$$

即两条往返复合在像上都是恒等。这就是 Galois 连接诱导的
「概念格 ≅ 闭集格」对偶的**算子层陈述**。

**证明**：`hexagon_left` 与 `hexagon_right` 的复合。 -/
theorem polar_roundtrip_on_image :
    (∀ A : Set K.GFCA,
        K.polarUp (K.polarDown (K.polarUp A)) = K.polarUp A)
      ∧ (∀ B : Set K.MFCA,
        K.polarDown (K.polarUp (K.polarDown B)) = K.polarDown B) :=
  ⟨fun A => K.polarUp_polarDown_polarUp A,
   fun B => K.polarDown_polarUp_polarDown B⟩

/-! ===========================================================================
    §5  与 `abstractStep` / `deconstructStep`（裁决 O，抽象–解构循环）的接口
    =========================================================================== -/

/-- **hexagon 等式在裁决 O 记法下的重述**（**接口引理，非新内容**）。

`Fate.Completeness` §5 把向上目光记为 `abstractStep`、向下目光记为
`deconstructStep`，并证了「两者构成伴随」（`abstract_deconstruct_adjoint`）。
本引理说明：**同一条伴随**在 `takeConcept` 记法下**正是** hexagon (H1)/(H2)——
即两处叙述指向同一件事实，**不构成两套平行理论**。

**内容**（与 hexagon 完全一致，只换记号）：

* `takeConcept ∘ abstractStep = abstractStep`
* `deconstructStep ∘ takeConcept = deconstructStep`

**证明**：`abstractStep`/`deconstructStep` 与
`polarUp`/`polarDown` 在 `Fate.Completeness` 中为 `rfl` 级相等
（`def abstractStep ... := K.polarUp O'`），故 `hexagon_left/right` 直接适用。 -/
theorem hexagon_in_loop_notation :
    K.takeConcept ∘ K.polarUp = K.polarUp
      ∧ K.polarDown ∘ K.takeConcept = K.polarDown :=
  ⟨K.hexagon_left_fun, K.hexagon_right_fun⟩

end FormalCtx

end

end FateV2.Rules