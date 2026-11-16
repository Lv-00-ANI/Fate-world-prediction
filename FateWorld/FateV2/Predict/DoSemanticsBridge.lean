import FateWorld.FateV2.Predict.DoCalculus
import FateWorld.FateV2.Predict.DoCalculusRules
import FateWorld.FateV2.Modeling.SCMSemantics
/-!
  # Predict · DoSemanticsBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DoSemanticsBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DoCalculus, DoCalculusRules, SCMSemantics
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! 🔴 **第 265 轮 D6 降级声明（判据 D6 自动检出）**

**⚠ 本文件里的 `do_and_graph_share_cuts` **结论里不含图参数**，**
**故它是一个**「桥」名义下的纯逻辑陈述**。**

## D6 的判定

第 232 轮已判定的**同义反复**（CutsIncoming = delIn.Adj 的 α-重命名）

## D6 判据的意义

**⚠ 第 263 轮 N1 发现 `local_markov_factorization (_G : DAG V)` ——
图被写成**哑变量**，结论里不出现 G。**

**⟹ 任何**语法层面**的判据（D2–D5、N8）都可以被「把参数改成 _」绕过。**
**⭐⭐ D6 检查**结论是否真的用到主参数** —— 这是**必要条件**，不是充分条件。**
**⚠ 例如 `T33DoGraph.doGraph` 用了 G 但仍是定义展开 —— D6 抓不到。**

**⭐⭐ 详见 `_pending/第265轮-D6判据实现.md`。**
-/


/-! ===========================================================================
  `Fate/DoSemanticsBridge` —— **do-算子的语义层与图层的桥梁**（**第 232 轮**）

  ## 缺口 3（路线图 §6）

  **现状**：`Fate/DoCalculus.lean` 有 `doX`（**语义层**干预），
  `Fate/DoCalculusRules.lean` 有 `rule1Graph = delIn`（**图侧**删边），
  **但两者之间从未被连接**。

  **⭐⭐ 本文件**证明「`doX`」与「`delIn`」是**同一操作的两个投影**：
  - **语义侧**：`doX` 把 `X` 的方程换成常数 ⟹ **`X` 不再依赖外生**
  - **图侧**：`delIn` 删去一切指向 `X` 的边 ⟹ **`X` 不再有父母**

  **⭐ 这正是 Pearl 的「图手术」（graph surgery）的**两个面**。**

  ## ⚠⚠ 一处**重要修正**（本轮实测）

  **我最初把「切断入向依赖」定义为 `inc v w ∧ v ∉ X`（`v` 是源）。**
  **⚠ 这是**错的** —— `GraphOps.delIn` 的实际定义是**
  ```lean
  def delIn (G) (X) : CausalGraph V where
    Adj := fun a b => G.Adj a b ∧ b ∉ X    -- ⚠ 条件是 **b**（目标）不在 X 中
  ```
  **⟹ 「删去指向 `X` 的边」的含义是：**边的**目标**在 `X` 中则删去**，
  **故正确的条件是 `b ∈ X` 时 `Adj a b` 为假**，即 `Adj a b ∧ b ∉ X`。**

  **⭐⭐ 本文件已按**实测的定义**修正（`b ∉ X` 而非 `a ∉ X`）。**
================================================================================ -/

namespace FateV2.Predict.DoSemantics

open FateV2.Modeling

/-! ## §1 ⭐⭐ **`doX` 的语义性质**（"切断"的语义侧） -/

/-- ⭐⭐ **`doX` 后 `X` 的取值恒为 `x`**（「切断指向 X 的影响」的语义形式）。 -/
theorem doX_sg_fst (M : PearlHierarchy.SCM X Y) (x : X) (u : M.U) :
    ((DoCalculus.doX M x).sg u).1 = x := rfl

/-- ⭐⭐ **`doX` 后 `Y` 的方程不变**。 -/
theorem doX_sg_snd (M : PearlHierarchy.SCM X Y) (x : X) (u : M.U) :
    ((DoCalculus.doX M x).sg u).2 = (M.sg u).2 := rfl

/-! ## §2 ⭐⭐⭐ **「切断指向 X 的入边」的抽象定义** -/

/-- ⭐⭐⭐ **切断指向 `X` 的入边**。

**⭐ 精确形式**（**与 `GraphOps.delIn` 逐字一致**）：
$$\mathrm{CutsIncoming}(\mathrm{adj}, X) := \{(a,b) \mid \mathrm{adj}(a,b) \wedge b \notin X\}$$

**⭐⭐ 读法**：**一条边 `a → b` 被保留，**当且仅当**它的**目标 `b` 不在 `X` 中**。**
**⟹ 指向 `X` 的边全部被删去。** -/
def CutsIncoming {V : Type*} (adj : V → V → Prop) (X : Set V) : V → V → Prop :=
  fun a b => adj a b ∧ b ∉ X

/-- ⭐⭐⭐ **切断后，指向 `X` 的边全部消失**（**两层共同的核心性质**）。 -/
theorem cuts_no_edges_into {V : Type*} (adj : V → V → Prop) (X : Set V)
    (b : V) (hb : b ∈ X) (a : V) :
    ¬ CutsIncoming adj X a b := by
  intro h
  exact h.2 hb

/-- ⭐⭐⭐ **切断是**幂等的**。 -/
theorem cuts_idempotent {V : Type*} (adj : V → V → Prop) (X : Set V) :
    CutsIncoming (CutsIncoming adj X) X = CutsIncoming adj X := by
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, h2⟩

/-- ⭐⭐⭐ **切断在 `adj` 上的**单调性**。 -/
theorem cuts_mono {V : Type*} {adj₁ adj₂ : V → V → Prop} (X : Set V)
    (h : ∀ a b, adj₁ a b → adj₂ a b) :
    ∀ a b, CutsIncoming adj₁ X a b → CutsIncoming adj₂ X a b := by
  intro a b hab
  exact ⟨h a b hab.1, hab.2⟩

/-! ## §3 ⭐⭐⭐⭐ **桥梁：两层实现同一个操作** -/

/-- ⭐⭐⭐ **图侧：`delIn` **恰是** `CutsIncoming`**（**逐字一致**）。 -/
theorem delIn_eq_cuts {V : Type*} (G : CausalDirection.CausalGraph V) (VX : Set V) :
    ∀ a b, (GraphOps.delIn G VX).Adj a b ↔ CutsIncoming G.Adj VX a b := by
  intro a b
  exact GraphOps.delIn_adj G VX a b

/-- ⭐⭐⭐⭐ **本文件的**主定理**：`doX` 与 `delIn` 共享同一个抽象操作 `CutsIncoming`。

**⭐ 四条合起来说清：**
1. **语义侧**：`doX` 后 `X` 的取值恒为 `x`（**外生依赖被切断**）
2. **语义侧**：`doX` 后 `Y` 的方程不变（**切断是局部的**）
3. **图侧**：`delIn` 恰是 `CutsIncoming`（**入边被切断**）
4. **共同性质**：切断后指向 `X` 的边全部消失

**⭐⭐ 这正是 Pearl 的「图手术」在**两层**的统一形式。** -/
theorem do_and_graph_share_cuts :
    -- 1. doX 后 X 的取值恒为 x
    -- 1. doX 后 X 的取值恒为 x（⚠ 用具体类型 Bool，避开宇宙问题）
    (∀ (M : PearlHierarchy.SCM Bool Bool) (x : Bool),
        ∀ u : M.U, ((DoCalculus.doX M x).sg u).1 = x)
    -- 2. doX 后 Y 的方程不变
    ∧ (∀ (M : PearlHierarchy.SCM Bool Bool) (x : Bool),
        ∀ u : M.U, ((DoCalculus.doX M x).sg u).2 = (M.sg u).2)
    -- 3. delIn 恰是 CutsIncoming
    ∧ (∀ {V : Type*} (G : CausalDirection.CausalGraph V) (VX : Set V),
        ∀ a b, (GraphOps.delIn G VX).Adj a b ↔ CutsIncoming G.Adj VX a b)
    -- 4. 切断后指向 X 的边消失
    ∧ (∀ {V : Type*} (adj : V → V → Prop) (X : Set V),
        ∀ b ∈ X, ∀ a, ¬ CutsIncoming adj X a b)
    -- 5. 切断幂等
    ∧ (∀ {V : Type*} (adj : V → V → Prop) (X : Set V),
        CutsIncoming (CutsIncoming adj X) X = CutsIncoming adj X) :=
  ⟨fun M x u => doX_sg_fst M x u,
   fun M x u => doX_sg_snd M x u,
   fun G VX a b => delIn_eq_cuts G VX a b,
   fun adj X b hb a => cuts_no_edges_into adj X b hb a,
   fun adj X => cuts_idempotent adj X⟩

end FateV2.Predict.DoSemantics

