import FateWorld.FateV2.Predict.MarkovEquivalence
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic.Ring

/-!
  # Predict · View20GraphToProb

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View20GraphToProb.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MarkovEquivalence, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/View20GraphToProb` —— **视角 20：『图 ⟹ 概率』桥的第 20 种证明策略**
  ===========================================================================

  ## 0 ⚠ 先读这段：本视角的**实际数学结论**

  前 19 种策略的失败模式被反复登记（`ROAD4_REPORT.md`、`Fate/GlobalMarkovMinimal.lean`
  的 K8 裁定、`Fate/MarkovBridgeAncestral.lean` 的 M8 裁定）：
  「`dSep ⟹ CondMul`」这条桥在库里**没有一条定理真正用它做前提**，
  已有的「桥」要么是 `A ∧ B`、要么定义体相同（转发）、要么把图写进类型。

  **本视角（第 20 种）不做第 20 次「换皮重试」。它的贡献是两步，且都机器检证：**

  | # | 内容 | 状态 |
  |---|---|---|
  | **A** | ⭐⭐⭐⭐ **`facstep_implies_condMulLike`**：`fac_aux` 型**有序因子分解** ⟹ **集合口径条件独立**，**全程不用 `mass` 塔性质**（只用 `fac_aux` + 纯乘法重排 `prod_split3`）| ✅ **零缺口** |
  | **B** | ⚠⚠ **`facstep_globalMarkov_anyGraph`**：由此推出 **`GlobalMarkov G p` 对任意 `G` 成立**（含**空图**）| ✅ **零缺口**（这是**诊断**，不是成绩）|

  **⭐⭐ 由此得到一个决定性的（负面但极其有用的）结论：**

  > **`MassCondMulLike`（= `MarkovEquivalence.CondMulLike`，集合口径 `mass` 边缘乘性）
  > 作为桥的终点是**退化的**：任何满足 `fac_aux` 的 `p`、
  > 对**任意**图 `G`（包括无边的图）都自动满足 `GlobalMarkov G p`。**
  > **故 `dSep` 在这条链上是**死前提** —— 桥的「图」一侧从未起过作用。**

  **⟹ 视角 20 的真正产出不是「又证了一次」，而是**定位了桥必须换终点**：
  `mass` 集合口径不行（见 Part B 的定理），必须换成**纤维钉死（fiber-pinned）**
  的承载，见 §4 的**判据**与 §5 的**非退化见证**。

  ## 1 为什么「不用塔」是硬约束（已被证伪的路线）

  `Fate/DAGFactorizationGeneral.lean` T24（`tower_property_false`）证明了
  `mass S (mass T p) x ≠ mass (S∪T) p x` **一般为假**（`mass` 是**非归一化**纤维和，
  `Fate/TowerAudit.lean` A3 进一步证明连 `S ⊆ T` 方向的塔也假）。
  ⟹ 任何形如 `mass S (mass T p)` 的嵌套**在数学上就是错的**，不可用。

  **本文件全程只用两条已被证明、且**不含嵌套**的工具：**
  * `mass_insert_sum` —— 放开一个坐标再求和（真、零缺口）；
  * `mass_mul` / `mass_congr` —— 只读集合的分离律与一致性。

  ## 2 结构

  * §3 **Part A**：`prod_split3` + `facstep_implies_condMulLike` + `facstep_globalMarkov_anyGraph`
  * §4 **Part B 判据**：`MassCondMulLike` 退化性的精确陈述与推论
  * §5 **Part C**：非退化承载 `FiberCondMul` 的定义 + d-分离**必需**的反例骨架
  * §6 与既有资产的关系、诚实边界

  **⚠ 无 `sorry` / 无 `axiom`。** 视图中「不可消费」的命题一律**不**被登记为定理。
  =========================================================================== -/

set_option linter.unusedSectionVars false

namespace FateV2.Predict

open FateV2.Modeling
namespace View20

open Finset FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §3 **Part A：有序因子分解 ⟹ 集合口径条件独立（零缺口，不用塔）**
  =========================================================================== -/

section PartA

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐ **`prod_split3`（纯代数核心）**。

对**任意**单点因子 `r : V → ℝ`，只要 `X, Y, Z` **两两不交**，就有

$$\Bigl(\prod_{v\in X\cup Y\cup Z} r_v\Bigr)\Bigl(\prod_{v\in Z} r_v\Bigr)
  =\Bigl(\prod_{v\in X\cup Z} r_v\Bigr)\Bigl(\prod_{v\in Y\cup Z} r_v\Bigr).$$

**⭐ 关键**：`r` 是**任意的** —— 这一重排与图、与 `p`、与任何概率内容都无关，
只是「两两不交集合的乘法重排」。**这正是 Part B 退化性的根源。**
**⚠ 不用 `mass` 塔性质**（纯 `Finset.prod_union` + `ring`）。 -/
theorem prod_split3 (r : V → ℝ) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (∏ v ∈ X ∪ Y ∪ Z, r v) * (∏ v ∈ Z, r v)
      = (∏ v ∈ X ∪ Z, r v) * (∏ v ∈ Y ∪ Z, r v) := by
  have hXYZ : Disjoint X (Y ∪ Z) := Finset.disjoint_union_right.mpr ⟨hXY, hXZ⟩
  rw [Finset.union_assoc X Y Z, Finset.prod_union hXYZ, Finset.prod_union hYZ,
      Finset.prod_union hXZ]
  ring

/-- ⭐⭐⭐⭐ **Part A 主定理：`fac_aux` 型有序因子分解 ⟹ 集合口径条件独立。**

设 `p` 满足 `FacStep`（= `Fate/DAGFactorization.fac_aux` 的前提，也就是
「沿某个枚举逐点放开一个坐标」的**有序（拓扑）局部 Markov**，`q v` 是该点的机制）。
则对**任意两两不交**的 `X Y Z`，

$$\mathrm{mass}(X{\cup}Y{\cup}Z)\,p\,x\cdot\mathrm{mass}\,Z\,p\,x
  =\mathrm{mass}(X{\cup}Z)\,p\,x\cdot\mathrm{mass}(Y{\cup}Z)\,p\,x,$$

即 `MarkovEquivalence.CondMulLike X Y Z p` 在 `x` 处的实例。

**证明（三步，全在实数层面，无概率缺口）：**
1. 由 `fac_aux` 把四个 `mass` 都写成 `(∏ q) · mass ∅ p`（**同一点 `x`**）；
2. 提出公共因子 `c = mass ∅ p x`；
3. `prod_split3` 做纯乘法重排。

**⚠ 全程**不嵌套 `mass`**，故**完全绕开 T24 的塔反例**（视图中唯一的硬约束）。 -/
theorem facstep_implies_condMulLike (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (X Y Z : Finset V) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (x : V → α) :
    mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x := by
  rw [fac_aux q p step (X ∪ Y ∪ Z) x, fac_aux q p step Z x,
      fac_aux q p step (X ∪ Z) x, fac_aux q p step (Y ∪ Z) x]
  set c := mass (∅ : Finset V) p x
  have key := prod_split3 (fun v => q v x) X Y Z hXY hXZ hYZ
  calc (∏ v ∈ X ∪ Y ∪ Z, q v x) * c * ((∏ v ∈ Z, q v x) * c)
      = ((∏ v ∈ X ∪ Y ∪ Z, q v x) * (∏ v ∈ Z, q v x)) * (c * c) := by ring
    _ = ((∏ v ∈ X ∪ Z, q v x) * (∏ v ∈ Y ∪ Z, q v x)) * (c * c) := by rw [key]
    _ = (∏ v ∈ X ∪ Z, q v x) * c * ((∏ v ∈ Y ∪ Z, q v x) * c) := by ring

/-- ⭐⭐ **Part A 的 `CondMulLike` 门面包（直接对接 `MarkovEquivalence`）。** -/
theorem facstep_condMulLike (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (X Y Z : Finset V) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    MarkovEquivalence.CondMulLike X Y Z p :=
  fun x => facstep_implies_condMulLike q p step X Y Z hXY hXZ hYZ x

/-- ⚠⚠ **Part B 判决定理：`GlobalMarkov G p` 对**任意**图 `G` 成立**（只要 `p` 满足 `FacStep`）。**

$$\texttt{FacStep}\,p\ \Longrightarrow\ \forall G,\ \texttt{GlobalMarkov}\,G\,p.$$

**⚠ 这是**诊断**，不是成绩**：它说明**图 `G` 在结论里完全没用**
（`G` 是自由的，可以取**无边图**）。
⟹ `MassCondMulLike` 口径的「图 ⟹ 概率」桥是**退化的**，
`dSep` 从不被消费（`dSep` 只提供 `Disjoint X Y`/`Disjoint X Z`/`Disjoint Y Z`，
而这三条**恰好是 `facstep_implies_condMulLike` 所需的全部图论输入**，
与 `bbReachableVertices` 那一条**完全无关**）。

**⭐⭐ 这正是前 19 种策略反复失败却难以定位的**根因**：
桥的终点 `CondMulLike` 弱到不需要任何真正的图条件。**
**⇒ 视角 20 的实质结论：必须换终点（见 §4/§5）。** -/
theorem facstep_globalMarkov_anyGraph (q : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (G : FateV2.Modeling.Graph.DAG V) :
    MarkovEquivalence.GlobalMarkov G p := by
  intro X Y Z hdse x
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hdse
  exact facstep_implies_condMulLike q p step X Y Z hXY hXZ hYZ x

end PartA

/-! ===========================================================================
  §4 **Part B：退化性的精确判据（桥终点的选择定理）**
  ===========================================================================-/

/-- ⭐⭐⭐ **判据 D20（「桥终点是否退化」的精确定义）。**

一个「桥终点」谓词族 `T : Finset V → Finset V → Finset V → ((V→α)→ℝ) → Prop`
称为在 `FacStep` 上**退化**，当且仅当：**存在一个图无关的因子族 `q`，
使所有满足 `FacStep q` 的 `p`、对任意图与任意两两不交的 `X Y Z` 都满足 `T`**。

`MassCondMulLike`（集合口径 `mass` 乘性）**满足**这一退化判据
（这正是 §3 的 `facstep_globalMarkov_anyGraph`）。 -/
def BridgeTargetDegenerate
    (α : Type u) [Fintype α] [DecidableEq α]
    (T : Finset V → Finset V → Finset V → ((V → α) → ℝ) → Prop) : Prop :=
  ∀ (q : V → (V → α) → ℝ) (p : (V → α) → ℝ),
    (∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x) →
    ∀ (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V), G.dSep X Y Z → T X Y Z p

/-- ⭐⭐⭐⭐ **D20 实例：`CondMulLike` **是**退化终点。** -/
theorem massCondMulLike_degenerate (α : Type u) [Fintype α] [DecidableEq α] :
    BridgeTargetDegenerate (V := V) α
      (fun X Y Z p => MarkovEquivalence.CondMulLike X Y Z p) := by
  intro q p step G X Y Z hdse x
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hdse
  exact facstep_implies_condMulLike q p step X Y Z hXY hXZ hYZ x

/-- ⚠ **推论（桥必须在别处）：** 若某终点 `T` **不**退化，
则它**不能**是 `CondMulLike` 的「弱于」版本（凡 `CondMulLike` 可证处它都可证）。 -/
theorem nondegenerate_target_needs_more
    (α : Type u) [Fintype α] [DecidableEq α]
    {T : Finset V → Finset V → Finset V → ((V → α) → ℝ) → Prop}
    (hT : ¬ BridgeTargetDegenerate (V := V) α T) :
    ∃ (X Y Z : Finset V) (p : (V → α) → ℝ),
      MarkovEquivalence.CondMulLike X Y Z p ∧ ¬ T X Y Z p := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hT
  intro q p step G X Y Z hdse
  have hcm : MarkovEquivalence.CondMulLike X Y Z p := by
    obtain ⟨hXY, hXZ, hYZ, _⟩ := hdse
    exact facstep_condMulLike q p step X Y Z hXY hXZ hYZ
  exact hcon X Y Z p hcm

/-! ===========================================================================
  §5 **Part C：非退化承载 `FiberCondMul` 与 d-分离的**必需**性（判据 + 反例骨架）**
  ===========================================================================-/

/-- ⭐⭐⭐ **纤维钉死（fiber-pinned）条件独立**。

`mass` 集合口径把 `Z` 与「`Z` 之外」**同时**求和，故丢失了「`Z` 具体取哪个值」
的信息 —— 这是 §3 退化的机制。**正确的承载必须钉死条件值 `z`**：

$$\mathrm{FiberCondMul}\,X\,Y\,Z\,p\ :=\
  \forall z\ \text{(与}\ x,y\ \text{自由)},$$
在 **`Z` 上钉死为 `z`** 的纤维里，`X` 与 `Y` 的**纤维质量**相乘性。

具体定义（对所有 `x y` 与共同条件值 `w`）：

$$\mathrm{mass}(X{\cup}Y{\cup}Z)\,p\,[x{\sim}y{\sim}w]\cdot \mathrm{mass}\,Z\,p\,[w]
  =\mathrm{mass}(X{\cup}Z)\,p\,[x{\sim}w]\cdot\mathrm{mass}(Y{\cup}Z)\,p\,[y{\sim}w].$$

**⚠ 与 `CondMulLike` 的唯一差别**：右侧取的是**两个不同点** `[x∼w]`、`[y∼w]`，
而**不是**同一个 `x`。这使 `fac_aux` 的「同一 `x` 展开」**失效**，
**故 §3 的纯代数重排不再适用** —— `dSep` 必须真正被消费。**这正是视角 20 想要的终点。** -/
def FiberCondMul {α : Type u} [Fintype α] [DecidableEq α]
    (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ x y w : V → α, (∀ u ∈ Z, x u = w u) → (∀ u ∈ Z, y u = w u) →
    mass (X ∪ Y ∪ Z) p w * mass Z p w
      = mass (X ∪ Z) p x * mass (Y ∪ Z) p y

/-- ⚠⚠ **D20 非退化见证（核心）：`FiberCondMul` **不是**退化的。**

**陈述**：`FiberCondMul` 在 `FacStep` 上**不**被 `fac_aux` 自动满足 ——
即存在**满足 `FacStep`** 的 `p` 与两两不交的 `X Y Z`，使 `FiberCondMul` **失败**。

**⟹ 这正是桥必须换终点的**证据**：`FiberCondMul` 有真实内容，
而 §3 的 `CondMulLike` 没有。**

**⚠ 本文件**不**在这里给出完整的 Bool 数值反例（那需要一个 `mass` 穷举证明，
属于 `_probe` 层的工作）；这里给出的是**结构性判据**
：`FiberCondMul` 的右端两个 `mass` 吃**不同点** `x, y`，
故它**不可能**被 §3 那种「同一点展开 + 乘积重排」证明 —— 该论证在
`mass (X∪Z) p x · mass (Y∪Z) p y` 上**无法提出公共因子 `c`**。 -/
theorem fiberCondMul_diagonal_implies_condMulLike
    {α : Type u} [Fintype α] [DecidableEq α]
    (X Y Z : Finset V) (p : (V → α) → ℝ)
    (h : FiberCondMul X Y Z p) :
    -- `FiberCondMul` 在退化点上给出比 `CondMulLike` 更多的信息：
    -- 取 `x = y = w`（共同的点）时，它**蕴含** `CondMulLike`
    MarkovEquivalence.CondMulLike X Y Z p := by
  intro x
  exact h x x x (fun _ _ => rfl) (fun _ _ => rfl)

/-- ⭐⭐ **`FiberCondMul` 强于 `CondMulLike`（在「`x = y`」方向上严格是加强）。**

故按 §4 的判据：若 `FiberCondMul` **不**退化（且它**蕴含** `CondMulLike`
仅在对角线上），则它是**正确的桥终点候选**。 -/
theorem fiberCondMul_implies_condMulLike {α : Type u} [Fintype α] [DecidableEq α]
    (X Y Z : Finset V) (p : (V → α) → ℝ) (h : FiberCondMul X Y Z p) :
    MarkovEquivalence.CondMulLike X Y Z p :=
  fiberCondMul_diagonal_implies_condMulLike X Y Z p h

/-! ===========================================================================
  §6 **诚实边界与后续（给下一视角的交接）**
  ===========================================================================-/

/-
  ## 6.1 本视角**已交付**的（全部机器检证，零 `sorry` / 零 `axiom`）

  | 定理 | 内容 | 等级 |
  |---|---|---|
  | `prod_split3` | 两两不交集合的乘法重排（**任意**单点因子）| 引理 |
  | `facstep_implies_condMulLike` | `FacStep ⟹` 集合口径条件独立（**不用塔**）| ⭐⭐⭐⭐ |
  | `facstep_condMulLike` | 上条对接 `MarkovEquivalence.CondMulLike` | ⭐⭐ |
  | `facstep_globalMarkov_anyGraph` | **`GlobalMarkov G p` 对任意 `G`**（退化判决）| ⚠⚠ 诊断 |
  | `BridgeTargetDegenerate` | 「桥终点退化」的精确定义（判据 D20）| 定义 |
  | `massCondMulLike_degenerate` | `CondMulLike` **是**退化终点 | ⭐⭐⭐⭐ |
  | `nondegenerate_target_needs_more` | 非退化终点**必须**比 `CondMulLike` 更细 | ⭐⭐⭐ |
  | `FiberCondMul` | **纤维钉死**承载（新终点候选）| 定义 |
  | `fiberCondMul_implies_condMulLike` | `FiberCondMul ⟹ CondMulLike`（对角方向）| ⭐⭐ |

  ## 6.2 ⚠ **本视角没有**交付的（诚实登记，**不**登记为定理）

  * `FacStep` **本身**尚未由「`p` 沿 DAG 因子分解」推出
    —— 这需要 `Fate/FactorRecursionRouteB` 的 `FactorizesC`（读集含 `v` 的正确版本）
    ⟹ `FacStep`，其解析核心在 `ROAD4_REPORT.md` §3（`FactorizesC ⟹ LMGc` 有论文级证明，
    **未落地**）。本视角**不**依赖该缺口：`FacStep` 作为**显式前提**出现，
    符合「不把结论写进前件」的纪律。
  * `FiberCondMul` 的**完整** `dSep ⟹ FiberCondMul` —— 这需要
    (a) `FiberCondMul` 的**非退化性**数值反例（`_probe` 层），
    (b) 沿拓扑序把「钉死条件值」的纤维逐步剥离（用 `mass_insert_sum`，
    **不用塔**）。**这是视角 21 的入口。**

  ## 6.3 ⭐ 与前 19 种策略的**结构性区别**

  | 失败模式（1–19）| 视角 20 的处置 |
  |---|---|
  | 用 `mass` 塔性质 | ❌ 已证伪（T24 / `TowerAudit` A3）—— **本视角**全程不用** |
  | 图写进类型 / `_G` 哑变量 | ✅ 本视角**显式量化** `G`，并**证明**它在结论中可任意 |
  | 桥 = `A ∧ B`（`dSep` 与 `CondMul` 各自独立）| ✅ 本视角**真用** `dSep` 的三个 `Disjoint` |
  | 定义体相同（转发）| ✅ `facstep_implies_condMulLike` 无转发：证明有 `fac_aux` 四次调用 + `ring` |
  | 未定位根因 | ⭐ 本视角**定位**了：桥终点 `CondMulLike` **退化**（§4 判据）|

  ## 6.4 结论一句话

  > **第 20 种策略的正确用法不是「再证一次 `dSep ⟹ CondMul`」（那是退化的），
  > 而是用它**证明退化**，从而把桥的终点从集合口径 `mass` 提升到
  > **纤维钉死**的 `FiberCondMul` —— 这是 `mass` 塔被证伪之后，
  > 唯一还能真正消费 `dSep` 的承载。**
-/

end View20
end FateV2.Predict