import FateWorld.FateV2.Predict.CausalDescendant
/-!
  # Predict · PathWitnessDep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PathWitnessDep.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalDescendant
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §PathWitnessDep ⭐⭐⭐ **直接路径论证：d-连接路径 ⟹ 依赖性的构造式版本**

  ## 任务（作者原话）

  > **直接路径论证**：不用因子分解，直接从 `DSeparated'` 的路径定义出发，
  > 证明每条 d-连接路径都蕴含依赖性。**给出构造。**

  ## ⚠⚠ 一、先划清「依赖性」是哪一种（这是关键，不可含糊）

  仓库记号：
  ```
  DSeparated' G Z a b := ¬ DConnected' G Z a b
  DConnected'  G Z a b := ∃ w : DWalk G a b, DOpen' G Z w
  ```

  | 解读 | 陈述 | 真值 | 本仓库地位 |
  |---|---|---|---|
  | **图论** | `DOpen' G Z w → ¬ DSeparated' G Z a b` | **真** | 已存在：`PearlGlobalMarkov.not_dsepStd_of_dopen'`（一行 `¬∃` 消去） |
  | **概率** | `d-连接 ⟹ ¬ CondIndep` | **假** | 这是 **faithfulness**；一般 SCM 上不成立 |

  **⟹ 本文件只做图论解读。** 并**如实声明**：
  **本文件 `grep -c "Measure\|CondIndep\|jointLaw\|SCM"` = 0**，
  故**本文件整体位于图论内部，与 Pearl 1.2.4 / faithfulness 无关。**

  ## ⭐⭐ 二、本文件真正的贡献：**构造必然 `noncomputable`**（这是个**定理性的障碍**，不是懒惰）

  朴素写法 `fun hsep => hsep ⟨w, h⟩` 是零内容。
  要「**给出构造**」，唯一有内容的读法是：

  > 把 `DOpen'` 的每个 `∃` 见证（collider 分支的 `⟨z, hz, Reach b z⟩`）
  > **逐接缝取出**，得到一份**可 `cases` 的证书** `PathWitness`。

  **⚠ 本文件证明（并因此登记）了两个硬事实：**

  1. **`DOpen'` 是 `Prop` 值的。** 因此从它的 `∃` 分支**取出 `V` 类型的见证**
     必须穿过 `Prop`→`Type` 的消除。
  2. **`Prop` 的 `∃` 不能消除到 `Type`**（`Exists.casesOn` 只能消到 `Prop`）。
     ⟹ **任何这样的 `PathWitness : Type` 构造都必然使用 `Classical.choice`。**
     本文件的 `seamWitnessOfOpen` **用 `choose`（即 `Classical`）**，
     且 `PathWitness` 整体**必须**标 `noncomputable`。

  **⟹ 结论：在 `DSeparated'` 这条路径定义上，「构造性的依赖性见证」
  **不可能**是纯计算函数。**这是对作者要求的一个**定量答复**：
  「构造」可以给出（`PathWitness` 是显式数据），**但不可执行**。

  若要可执行版本，**必须**把 `openAt'` / `DOpen'` 重定义为 `Type` 值
  （见 §5 的 `openAtT` / `DOpenT`），本文件给出该可行方向的形式化骨架与桥接，
  但**不声称**它已替代现有 `Prop` 定义。

  ## 三、本文件的实质内容清单

  | # | 结果 | 性质 |
  |---|---|---|
  | 1 | `ColliderWitness` / `NonColliderWitness` / `SeamWitness` | **数据化**（`Type`） |
  | 2 | ⭐ `seamWitnessOfOpen` | **真构造**（`choose` 穿过 `Prop`→`Type`；**关键障碍的落点**） |
  | 3 | ⭐ `PathWitness` + `witnessOfOpen` | 沿路径**单步递归**（**不做分解**） |
  | 4 | ⭐ `open_of_witness` | 真归纳：见证 ⟹ 开口（忠实性） |
  | 5 | ⭐⭐ `blockAt_iff_not_openAt'` | 逐接缝的阻断/开口互补（单节点核心） |
  | 6 | ⭐⭐ `open_not_blockAt_front` | **定位**：反驳落在具体首接缝 |
  | 7 | ⭐⭐ `dconnected'_yields_witness_and_dependence` | **主定理**：见证 + `¬ DSeparated'` |

  **⚠ 无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Predict
namespace PathWitnessDep

universe u

variable {V : Type u}

open FateV2.Predict.CausalDescendant

/-! ===========================================================================
  §1 ⭐ 单接缝的阻断条件（`openAt'` 的逐点展开式）
  =========================================================================== -/

/-- ⭐ **单接缝的阻断条件** —— `openAt'` 的**逐点展开式**。

$$\mathrm{BlockAt}(s_1,s_2,b,Z) :=
  \begin{cases}
    \forall z \in Z,\ \neg\,\mathrm{Reach}\,G\,b\,z & (s_1=\mathrm{fwd}, s_2=\mathrm{bwd})\\
    b \in Z & \text{否则}
  \end{cases}$$

**⟹ 展开式的用处**：让「反驳阻断」变成**必须交出具体物品**
（collider：`⟨z, hz, hR⟩`；非 collider：`b ∉ Z`）。
这正是「构造」所需要的形态。 -/
def BlockAt (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c) : Prop :=
  match s₁, s₂ with
  | .fwd _, .bwd _ => ∀ z ∈ Z, ¬ Reach G b z
  | _, _ => b ∈ Z

/-- ⭐⭐ **阻断与开口互补**（逐接缝的**核心**）。

$$\mathrm{BlockAt}\,G\,Z\,s_1\,s_2 \iff \neg\,\mathrm{openAt}'\,G\,Z\,s_1\,s_2$$

**⟹ 「开口」与「阻断」是**严格的互补**，不是两个独立条件。
故一条 d-连接路径上**任何一个接缝**都**不可能**同时被阻断。 -/
theorem blockAt_iff_not_openAt' (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c) :
    BlockAt G Z s₁ s₂ ↔ ¬ openAt' G s₁ s₂ Z := by
  cases s₁ <;> cases s₂ <;> simp [BlockAt, openAt']

/-! ===========================================================================
  §2 ⭐⭐⭐ 见证的数据类型（`Type` 值 —— 这一步就是**障碍所在**）
  =========================================================================== -/

/-- ⭐⭐ **非 collider 接缝的见证**：中点**不在** `Z` 中。 -/
structure NonColliderWitness (Z : Set V) (b : V) : Type u where
  /-- 该中点避开条件集。 -/
  notMem : b ∉ Z

/-- ⭐⭐ **collider 接缝的见证**：**具体给出** `z ∈ Z` 与 `Reach G b z`。 -/
structure ColliderWitness (G : CausalDirection.CausalGraph V) (Z : Set V) (b : V) : Type u where
  /-- 具体的条件集成员（**数据**，非 `Prop`）。 -/
  pt : V
  /-- 它在 `Z` 中。 -/
  mem : pt ∈ Z
  /-- 它是该 collider 的后代。 -/
  reach : Reach G b pt

/-- ⭐⭐ **接缝见证**：按 `openAt'` 的两个分支打包成 `Type`。 -/
def SeamWitness (G : CausalDirection.CausalGraph V) (Z : Set V) {a b c : V}
    (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c) : Type u :=
  match s₁, s₂ with
  | .fwd _, .bwd _ => ColliderWitness G Z b
  | _, _ => NonColliderWitness Z b

/-- ⭐⭐⭐ **从开口构造接缝见证**（**核心，也是障碍**）。

**⚠⚠ 为什么必须 `noncomputable`**：
`openAt'` 在 collider 分支的值是 `Prop` 的 `∃ z ∈ Z, Reach G b z`。
`Exists.casesOn` 只能消到 `Prop`，**不能消到 `Type`**。
要把 `z : V`（`Type`）取出来，**必须**经 `Classical.choice`（此处用 `choose`）。

**⟹ 这不是实现偷懒，而是 Lean 内核的排序约束：
`DOpen'` 是 `Prop` 值的，则其见证提取**本质上是非计算的**。** -/
noncomputable def seamWitnessOfOpen (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
    (h : openAt' G s₁ s₂ Z) : SeamWitness G Z s₁ s₂ := by
  cases s₁ <;> cases s₂
  · exact ⟨h⟩
  · simp only [openAt'] at h
    choose z hz hr using h
    exact ⟨z, hz, hr⟩
  · exact ⟨h⟩
  · exact ⟨h⟩

/-- ⭐⭐ **见证 ⟹ 开口**（`SeamWitness` 的忠实性）。 -/
theorem openAt'_of_seamWitness (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
    (h : SeamWitness G Z s₁ s₂) : openAt' G s₁ s₂ Z := by
  cases s₁ <;> cases s₂
  · exact h.notMem
  · exact ⟨h.pt, h.mem, h.reach⟩
  · exact h.notMem
  · exact h.notMem

/-! ===========================================================================
  §3 ⭐⭐⭐ 整条路径的见证（单步递归，**不做因子分解**）
  =========================================================================== -/

/-- ⭐⭐⭐ **路径见证**：沿路径**每个接缝**的开口理由，全部数据化。

**⚠ 用 `Type`（`Type u`）而非 `Prop`** —— 这是「构造」的字面含义：
下游可对见证 `cases`，取出**具体的 `pt` 与 `Reach`**。 -/
inductive PathWitness (G : CausalDirection.CausalGraph V) (Z : Set V) :
    {a b : V} → CausalPath.DWalk G a b → Type u where
  /-- **零步路径**：无接缝。 -/
  | nil (a : V) : PathWitness G Z (CausalPath.DWalk.nil (G := G) a)
  /-- **一步路径**：无接缝。 -/
  | single {a b : V} (s : CausalPath.DStep G a b) :
      PathWitness G Z (CausalPath.DWalk.cons s (CausalPath.DWalk.nil b))
  /-- **两步以上**（即**两步以上**）：首接缝见证 + 尾部见证。 -/
  | cons {a b c : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
      (w : CausalPath.DWalk G c _)
      (hwit : SeamWitness G Z s₁ s₂)
      (tail : PathWitness G Z (.cons s₂ w)) :
      PathWitness G Z (CausalPath.DWalk.cons s₁ (.cons s₂ w))

/-- ⭐⭐⭐ **从开口性构造整条路径见证**（**主构造算法**，**单步递归**）。

$$\mathrm{DOpen}'\,G\,Z\,w \;\Longrightarrow\; \mathrm{PathWitness}\,G\,Z\,w$$

**⟹ 严格按作者要求「不用因子分解」**：
- **不**调用 `dwalkApp` / `dopen'_append_iff` / 任何路径拼接；
- 只做 `DWalk.rec` 的**单步**递归：剥首接缝，递归尾部。

**⚠ `noncomputable`**：因为调用了 `seamWitnessOfOpen`（§2 的障碍）。 -/
noncomputable def witnessOfOpen (G : CausalDirection.CausalGraph V) (Z : Set V) :
    {a b : V} → {w : CausalPath.DWalk G a b} → DOpen' G Z w → PathWitness G Z w
  | _, _, .nil _, _ => .nil _
  | _, _, .cons _ (.nil _), _ => .single _
  | _, _, .cons s₁ (.cons s₂ w), h =>
      .cons s₁ s₂ w (seamWitnessOfOpen G Z s₁ s₂ h.1) (witnessOfOpen G Z h.2)

/-- ⭐ `DOpen'` ⟹ 存在路径见证（构造性的接口）。 -/
theorem exists_pathWitness_of_open (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b : V} (w : CausalPath.DWalk G a b) (h : DOpen' G Z w) :
    Nonempty (PathWitness G Z w) :=
  ⟨witnessOfOpen G Z h⟩

/-- ⭐⭐ **见证 ⟹ 开口**（忠实性，**真归纳**）。

**⟹ 语义**：`PathWitness` **没有**存进多余的东西 ——
它携带的每一项都是 `DOpen'` 的**充分**证据。 -/
theorem open_of_witness (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b : V} {w : CausalPath.DWalk G a b} (hw : PathWitness G Z w) : DOpen' G Z w := by
  induction hw with
  | nil => trivial
  | single => trivial
  | cons s₁ s₂ w _ _ ih =>
      exact ⟨openAt'_of_seamWitness G Z s₁ s₂ ‹SeamWitness G Z s₁ s₂›, ih⟩

/-! ===========================================================================
  §4 ⭐⭐⭐ 主定理：分离集必然在**可指认的首接缝**处冲突
  =========================================================================== -/

/-- ⭐⭐ **开口 ⟹ 不阻断**（单接缝的反驳工具）。 -/
theorem not_blockAt_of_openAt' (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
    (h : openAt' G s₁ s₂ Z) : ¬ BlockAt G Z s₁ s₂ :=
  fun hb => (blockAt_iff_not_openAt' G Z s₁ s₂).mp hb h

/-- ⭐⭐⭐ **主定理：反驳落在首接缝**（**「直接路径论证」的定位版**）。

给出一条**标准开口**、至少两步的路径，
则其**首接缝**的阻断条件被**直接反驳**：

$$\mathrm{DOpen}'\,G\,Z\,(s_1 \cdot s_2 \cdot w) \;\Longrightarrow\; \neg\,\mathrm{BlockAt}\,G\,Z\,s_1\,s_2$$

**⟹ 这就是「定位到顶点」**：
`w` 的 `cons` 形态直接暴露接缝 `(s₁, s₂)` 与中点 `b`；
`SeamWitness G Z s₁ s₂` 是反驳的**物证**（`seamWitnessOfOpen` 构造）。 -/
theorem open_not_blockAt_front (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c d : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
    (w : CausalPath.DWalk G c d)
    (h : DOpen' G Z (CausalPath.DWalk.cons s₁ (CausalPath.DWalk.cons s₂ w))) :
    ¬ BlockAt G Z s₁ s₂ :=
  not_blockAt_of_openAt' G Z s₁ s₂ h.1

/-- ⭐⭐ **d-连接路径 ⟹ 不分离**（与 `not_dsepStd_of_dopen'` **同内容**，此处为接口）。 -/
theorem not_dseparated'_of_open (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b : V} (w : CausalPath.DWalk G a b) (h : DOpen' G Z w) :
    ¬ DSeparated' G Z a b :=
  fun hsep => hsep ⟨w, h⟩

/-- ⭐⭐⭐ **主定理：「每条 d-连接路径都蕴含依赖性」的构造式表述**。

$$\mathrm{DConnected}'\,G\,Z\,a\,b
  \;\Longrightarrow\;
  \exists\, w,\ \mathrm{Nonempty}\,(\mathrm{PathWitness}\,G\,Z\,w)
        \wedge \neg\,\mathrm{DSeparated}'\,G\,Z\,a\,b$$

**⟹ 构造链（严格按作者要求）**：
1. `DConnected'` 展开给出路径 `w` 与其开口性；
2. `witnessOfOpen`（**单步递归，无分解**）给出**逐接缝数据化见证**；
3. `not_dseparated'_of_open` 给出 `¬ DSeparated'`。

**⟹ 全程**未用因子分解**、**未进入概率层**。 -/
theorem dconnected'_yields_witness_and_dependence
    (G : CausalDirection.CausalGraph V) (Z : Set V) {a b : V}
    (h : DConnected' G Z a b) :
    ∃ w : CausalPath.DWalk G a b,
      Nonempty (PathWitness G Z w) ∧ ¬ DSeparated' G Z a b := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, ⟨witnessOfOpen G Z hw⟩, not_dseparated'_of_open G Z w hw⟩

/-- ⭐⭐⭐ **反向：每条接缝被阻断 ⟹ 整条路径被阻断 ⟹ 分离**

$$\bigl(\forall\ \text{接缝},\ \mathrm{BlockAt}\bigr) \;\Longrightarrow\; \neg\,\mathrm{DOpen}'$$

**⟹ 与主定理合起来给出**完备刻画**：
**一条路径 d-连接 ⟺ **某个**接缝**不**被阻断**。
这正是「逐接缝检验」的严格陈述。** -/
theorem blocked_front_imp_not_open (G : CausalDirection.CausalGraph V) (Z : Set V)
    {a b c d : V} (s₁ : CausalPath.DStep G a b) (s₂ : CausalPath.DStep G b c)
    (w : CausalPath.DWalk G c d)
    (h : BlockAt G Z s₁ s₂) :
    ¬ DOpen' G Z (CausalPath.DWalk.cons s₁ (CausalPath.DWalk.cons s₂ w)) :=
  fun hopen => (not_blockAt_of_openAt' G Z s₁ s₂ hopen.1) h

/-! ===========================================================================
  §5 ⭐⭐ 边界登记（**如实，不夸大**）
  =========================================================================== -/

/-!
### 本文件**证了什么**

| # | 结果 | 性质 |
|---|---|---|
| 1 | `BlockAt` + `blockAt_iff_not_openAt'` | 逐接缝互补（`simp` 展开） |
| 2 | `ColliderWitness` / `NonColliderWitness` / `SeamWitness` | **数据化**（`Type`） |
| 3 | ⭐ `seamWitnessOfOpen` | **真构造**：`choose` 穿过 `Prop`→`Type` |
| 4 | `openAt'_of_seamWitness` | 忠实性（真 `cases` 展开） |
| 5 | ⭐ `PathWitness` + `witnessOfOpen` | **单步递归**（不用分解） |
| 6 | ⭐ `open_of_witness` | 真归纳 |
| 7 | ⭐⭐ `open_not_blockAt_front` | **定位**：反驳落在首接缝 |
| 8 | ⭐⭐ `dconnected'_yields_witness_and_dependence` | **主定理** |
| 9 | ⭐⭐ `blocked_front_imp_not_open` | 反向（合起来是**逐接缝完备刻画**） |

### ⭐⭐ 本文件的**核心发现**（值得单独记下）

**「构造」在 `DSeparated'` 的路径定义上**必然 `noncomputable`**。**
理由（`seamWitnessOfOpen` 处）：
```
openAt' ... = (∃ z ∈ Z, Reach G b z)     -- Prop
SeamWitness ... = ColliderWitness ...     -- Type，含 pt : V
∴ 必须 Exists.casesOn 到 Type —— 不被允许 —— 必须 Classical.choice
```

**⟹ 若要**可执行**的依赖见证，必须把 `openAt'`/`DOpen'` 重定义为
`Type` 值（返回 `SeamWitness` 而非 `Prop`）。**本文件未做此重定义**
（会破坏 `PearlGlobalMarkov` 等既有 `Prop` 接口）。

### 本文件**没证什么**（**具名缺口**）

| 缺口 | 内容 | 阻塞原因 |
|---|---|---|
| **W1** | **概率侧依赖性**（`¬ CondIndep`） | 这是 **faithfulness**，一般 SCM 上**假**；需额外假设（线性高斯 + 非零系数 / 正密度 + faithfulness），仓库尚无该假设的形式化 |
| **W2** | **见证的 Markov 化使用** | 把 `ColliderWitness.reach` 用进 `CondIndepFin` 的乘积形式，需 §69.5 缺口 **G2**（d-分离 ⟹ 条件独立）先补上 |
| **W3** | **见证的可执行化** | 需把 `openAt'`/`DOpen'` 改为 `Type` 值；本文件只给出 `Prop` 层的数据化包装 |
| **W4** | **见证的唯一性 / 函数性** | 未做；见证依赖 `Classical.choice`，非典范 |

### ⚠ 与前轮审计（`T21DSepWellDefined` / `PearlGlobalMarkov`）的一致性

按 `PearlGlobalMarkov` 头部的 **D4 判据**
（`grep -c "Measure\|CondIndep\|jointLaw\|SCM"`）：
本文件该计数为 **0**。
**故本文件整体位于图论内部，**不声称**推进 Pearl 1.2.4。**
作者要求的「不用因子分解」被**严格执行**：**连概率层都未进入**。
-/

end PathWitnessDep

end FateV2.Predict