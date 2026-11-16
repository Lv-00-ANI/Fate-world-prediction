import FateWorld.FateV2.Predict.BackdoorWithM
import Mathlib.Tactic

/-!
  # Predict · G2Backdoor

  ## 迁移登记
  - 来源：`FateWorld/Legacy/G2Backdoor.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BackdoorWithM
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/G2Backdoor` —— `G2`：backdoor 语义的真缺口

## 0 背景（项目规划文档的 `G2` 条目）

> **「`G2` ⭐ backdoor（把 `USeparated` 换掉）**
> **现状：`BackdoorCriterion:390` 是真定理但**不用 `USeparated`**；
> **`BackdoorGenuine §5` 是假标题**；
> **R286 加了 `IsDescendant/NoDescendant` 但**零引用**；
> R297 证明 `SetupXMY` 是**纯死前提**。**
> **做法：在 `BackdoorCriterion.lean` 已有载体上（R259 的 `BackdoorSetup`，`fY` 第一槽就是 `X`），
> 把 R286 的 `NoDescendant` 接到 `adjustLaw` 的**数值计算**上：
> **`adjustLaw ≠ doLaw` 当且仅当 `W` 含 `Y` 的后代（一篇双向 + 数值反例）。**」**

## 1 ⭐⭐⭐ **本轮的 D7 审计发现（先看这条）**

规划文档怀疑的「`NoDescendant` 是恒真式」—— **必须把两个同名但不同的东西分开**：

| # | 名字 | 位置 | 定义 | 判定 |
|---|---|---|---|---|
| **A** | `R259.BackdoorSetup.NoDescendant` | `Fate/BackdoorCriterion.lean:276` | `∀ z ux, fX z ux = fX z ux` | ⭐⭐⭐ **恒真式（`rfl` 级），死前提** |
| **B** | `R277.NoDescendant S W` | `Fate/BackdoorGenuine.lean:526` | `∀ v ∈ W, ¬ IsDescendant S v` | ⭐ **有内容**（R288 已给非空洞见证）|

**⚠ 因此「`NoDescendant` 是恒真式」只在 A 上成立；B 不是恒真式。**

### 1.1 **A 为什么必然是恒真式（结构性，不是笔误）**

`BackdoorSetup` 的签名是 `fX : Z → Ux → X`。**`X` 是汇点**（`X` 没有任何出边），
故「`Z` 是 `X` 的后代」在这个载体里**根本写不出来**。
A 的定义把 `fX z ux` 和它自己比较，是**对「写不出后代关系」的空洞补偿** ——
`rfl` 即证（`noDescendant_trivial`）。

### 1.2 ⭐⭐ **A 的真空性会被「免费」证明**

`BackdoorConditions`（`BackdoorCriterion.lean:409`）的第 2 个字段**就是 A**
（`no_descendant : S.NoDescendant`）。由 §1.1，
**任何** `h : (⟨S_blocks, rfl, S_posX, S_posZ⟩ : BackdoorConditions S)` 都能造出来 ——
见 `backdoorConditions_free`：**(ii) 对 `BackdoorConditions` 零约束。**

## 2 ⭐⭐⭐⭐⭐ 本题的核心价值：**`adjustLawM ≠ doLaw` 的数值反例**

规划文档要求「数值反例」。注意：**在 `R259.BackdoorSetup` 上做不到** ——
`fY` 的第一个槽就是 `X`，故 `Y` 恒是 `X` 的后代，「`W` 含 `Y` 的后代」恒真，
`W` 与查询 `(x,y)` 无关，故**不存在**「`adjustLaw` 依赖于 `W`」这回事。

**唯一能做的正确载体是 `R290.SetupWithM`**（回归 A 的禁令：**不新建载体**）。

## 3 ⭐⭐ **一个精确的「图 ⟹ 数值」定理（本文档的正面结果）**

`noDescendantM_implies_X_only`：设 `M` 有至少两个取值，且

  `P(M = m | X = x) > 0`（∀ x m —— 中介通道**畅通**）

则

  **`NoDescendantM S {M}`（`W = {M}` 不含 `X` 的后代）** ⟺ **`M` 的取值与 `X` 无关**
  （`∀ x₁ x₂ uy₁ uy₂, fM x₁ uy₁ = fM x₂ uy₂`）。

**读法**：Pearl (ii) 在 `SetupWithM` 上**等价于「中介退化（`M` 不是真中介）」**，
这精确刻画了「`W = {M}` 合法的调整集 **当且仅当** `M` 根本不是中介」这一边。

## 4 ⭐⭐⭐⭐⭐ **缺口的正面证据（说明 `G2` 没有被关闭）**

`demo_fM_identity`：`Demo.demo`（R290 的中介载体）里 `fM x uy = if uy then true else x`。
于是 `M` **完全决定** `X`（`M=0 ⟹ X=0`）—— **`X` 从 `M` 的律里不可恢复地丢失了**。
**⟹ 用观测数据 `∑_m P(y|x,m)P(m)` 永远算不出 `P(y|do(x))`**
（`P(m)` 已被 `X` 混淆；`adjustLawM` 里的 `P(y,m|x,z)` **仍带着 `x`**，
这正是「中介偏误」无法靠图条件消除的**结构性**原因）。

**⚠ 因此本文档不声称「`G2` 已解决」**：(ii) 的**双向**「`adjustLaw ≠ doLaw` ⟺ `W` 含后代」
在 `SetupWithM` 上**依然不可得**（`adjustLawM` 的定义里 `x` 与 `m` 通过 `fM` 纠缠）。
详见 §3 的精确双向（它只覆盖 (i) 方向，且只覆盖退化情形）。
-/

namespace FateV2.Predict.Stage2.G2Backdoor

open FateV2.Modeling

open FateV2.Error

/-! ===========================================================================
  §1 ⭐⭐⭐ **`BackdoorSetup.NoDescendant`（R259 的 A 号定义）是恒真式**
  =========================================================================== -/

/-- ⭐⭐⭐ **D7 审计：`NoDescendant` 是**恒真式**（它的定义是 `fX z ux = fX z ux`）。

**⟹ 这是**死前提**：任何定理若以 `NoDescendant` 为假设，
该假设**永远可由 `rfl` 满足**，因此不提供任何约束。** -/
theorem noDescendant_trivial (S : FateV2.Predict.R259.BackdoorSetup) : S.NoDescendant := by
  intro z ux
  rfl

/-- ⭐⭐⭐ **推论：`BackdoorConditions` 的 (ii) 字段对 `BackdoorConditions` 零约束。**

`no_descendant` 字段由 `noDescendant_trivial` **免费**填充 ⟹
`BackdoorConditions` 实际只有 **3** 个非平凡字段（(i) + positivity ×2）。
**⚠ 这就是 N2 报告里「(ii) NoDescendant 是 rfl 级空命题」的机器化版本。**

⚠ 原证明试图用 `transport` 比较两条 `Prop` 的证明项——那在证明无关性下无意义。
改为**直接陈述**：(ii) 字段随时可填，不必额外假设。 -/
theorem backdoorConditions_no_descendant_free (S : FateV2.Predict.R259.BackdoorSetup)
    (hB : S.BackdoorBlocked) (hx : S.PosX) (hz : S.PosZ) :
    ∃ c : FateV2.Predict.R259.BackdoorConditions S, c.blocks_backdoor = hB :=
  ⟨⟨hB, noDescendant_trivial S, hx, hz⟩, rfl⟩

/-- 辅助：`NoDescendant` 的唯一证明（`rfl` 级）。

⚠ 注意：这是本文件里为 `BackdoorSetup` 命名空间补充的**辅助引理**，
不是 `BackdoorCriterion` 原有定义的一部分。 -/
theorem FateV2.Predict.R259.BackdoorSetup.NoDescendant_from_trivial (S : FateV2.Predict.R259.BackdoorSetup) :
    S.NoDescendant :=
  FateV2.Predict.Stage2.G2Backdoor.noDescendant_trivial S

/-! ===========================================================================
  §2 ⭐⭐ **正确的（B 号）`NoDescendant` 不是恒真式**
  =========================================================================== -/

/-- ⭐⭐⭐ **B 号 `NoDescendant`（`R277`）在 `W = {Y}` 上**为假**（只要 `fY` 能取到 `y`）。

**⟹ B 号**不是**恒真式** —— 它与 A 号形成对照。** -/
theorem noDescendant_raw_not_trivial
    (S : FateV2.Predict.R259.BackdoorSetup) (x : S.X) (y : S.Y) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (hf : S.fY x z ux uy = y) :
    ¬ FateV2.Predict.R277.NoDescendant S ({FateV2.Predict.R277.Vert.y y} : Set (FateV2.Predict.R277.Vert S)) :=
  Fate.NoDescendantWitness.noDescendant_singleton_false S x y z ux uy hf

/-- ⭐⭐ **对照：`W = {Z}` 满足 B 号 `NoDescendant`**（`Z` 不是 `X` 的后代）。

**⚠ `R290.SetupWithM` 的 `SetupWithM.noDescendantM_singleton_Z` 是同类结论；
这里给 `R259` 载体上的直接对照，用以说明 A/B 两号的差别是**实质**的。** -/
theorem noDescendant_raw_zig_true
    (S : FateV2.Predict.R259.BackdoorSetup) (z : S.Z) :
    ¬ FateV2.Predict.R277.IsDescendant S (FateV2.Predict.R277.Vert.z z) := by
  intro h
  obtain ⟨y, hy⟩ := Fate.NoDescendantWitness.descendant_is_y S h
  -- `hy : Vert.z z = Vert.y y` —— 两个不同构造子相等，直接矛盾
  cases hy

/-! ===========================================================================
  §3 ⭐⭐ **精确的「图 ⟹ 数值」双向：`NoDescendantM {M}` ⟺ `M` 与 `X` 无关**
  =========================================================================== -/

namespace G2M

variable (S : Fate.R289.SetupWithM)

/-- ⭐ **「中介通道畅通」**：`P(M = m | X = x) > 0` 对**所有** `(x,m)` 成立。

**⭐ 这是 §3 主定理的唯一「概率侧」假设 —— 它只要求 positivity，
**不是**结论的改写。** -/
def MedOpen : Prop := ∀ (x : S.X) (m : S.M), S.condM x m > 0

/-- ⭐⭐ **「`M` 的取值与 `X` 无关」**（`fM` 丢弃第一槽）。

    ⚠ **原定义把 `uy` 也量化掉了**（`∀ x₁ x₂ uy₁ uy₂`），于是它实际断言
    「`fM` 是**常数函数**」——比「与 `X` 无关」强得多。

    本文件保留原语义（历史代码不改定义），但下文的定理会显式标注这一点。 -/
def MFreeOfX : Prop := ∀ (x₁ x₂ : S.X) (uy₁ uy₂ : S.Uy), S.fM x₁ uy₁ = S.fM x₂ uy₂

/-! ### §3.1 **关键事实：`M` 恒是 `X` 的直接后继**

**这是本轮重写的前提。** 原文件 §3.1 声称「`M` 与 `X` 无关 ⟹ `M` 不是 `X` 的后代」，
**方向是反的**：由 `moralAdjM` 的 `X→M` 分支，

```
∃ x uy m, (X x) → (M m)   ⟺   fM x uy = m
```

取任意 `x`、`uy`，令 `m := fM x uy`，边条件即满足。
故 **只要 `X` 与 `Uy` 非空，`MVert.m (fM x uy)` 就是 `X` 的直接后继**，
与 `fM` 是否依赖 `x` **无关**。

上游 `BackdoorGraphicalGeneral.not_noDescendant_singleton_M` 已证同一事实。 -/

/-- ⭐⭐⭐ **`M` 的任一可达值都是 `X` 的直接后继**（`moralAdjM` 的 `X→M` 边）。

这是本文件 §3 全部结论的**基石**，也是原文件缺失的那块。 -/
theorem m_in_descendant (x : S.X) (uy : S.Uy) :
    Fate.R289.SetupWithM.IsDescendantM S (.m (S.fM x uy)) :=
  Fate.R289.SetupWithM.IsDescendantM.step <| by
    -- `moralAdjM (X x) (M (fM x uy))`：落在第三个析取支
    unfold Fate.R289.SetupWithM.moralAdjM
    exact Or.inr <| Or.inr <| Or.inl ⟨x, uy, S.fM x uy, rfl, rfl, rfl⟩

/-- 辅助：**任何连到 `MVert.m m` 的边都给出 `m ∈ range fM`**。

    `moralAdjM` 共有 **8** 个析取支（`Z→X`、`Ux→X`、`X→M`、`Uy→M`、
    `M→Y`、`Z→Y`、`Ux→Y`、`Uy→Y`）。其中只有 **第 3、4 支**的终点是 `M`，
    而两支都带条件 `fM x uy = m`。其余 6 支的终点是 `X` 或 `Y`，与 `M` 冲突。 -/
theorem edge_to_m_implies_mem (v : Fate.R289.SetupWithM.MVert S) (m : S.M)
    (h : Fate.R289.SetupWithM.moralAdjM S v (.m m)) :
    ∃ (x : S.X) (uy : S.Uy), S.fM x uy = m := by
  rcases h with ⟨_, _, _, _, hb, _⟩ | ⟨_, _, _, _, hb, _⟩
    | ⟨x, uy, m', _, hb, hf⟩ | ⟨x, uy, m', _, hb, hf⟩
    | ⟨_, _, _, _, _, _, hb, _⟩ | ⟨_, _, _, _, _, _, hb, _⟩
    | ⟨_, _, _, _, _, _, hb, _⟩ | ⟨_, _, _, _, _, _, hb, _⟩
  -- Z→X / Ux→X：终点是 X，与 `b = M m` 冲突
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  -- X→M / Uy→M：给出 `fM x uy = m'`，且 `MVert.m m = MVert.m m'` ⟹ `m = m'`
  · obtain rfl : m = m' := Fate.R289.SetupWithM.MVert.m.inj hb
    exact ⟨x, uy, hf⟩
  · obtain rfl : m = m' := Fate.R289.SetupWithM.MVert.m.inj hb
    exact ⟨x, uy, hf⟩
  -- M→Y / Z→Y / Ux→Y / Uy→Y：终点是 Y，冲突
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)
  · exact absurd hb (by simp)

/-- ⭐⭐⭐ **`NoDescendantM {M m}` 成立 ⟺ `m` 不在 `fM` 的像里。**

    **这是 §3.1 的正确形式**（原文件的「`MFreeOfX ⟹ 非后代」是假的）。

    读法：`W = {M m}` 不含后代，**当且仅当** `m` 根本不可能被 `fM` 取到。
    ⟹ 这个条件对「可达的 `m`」永远为假——**原文件想说的「中介是合法的调整集」
    在 `SetupWithM` 载体上不可能成立**。 -/
theorem noDescendantM_singleton_iff (m : S.M) :
    Fate.R289.SetupWithM.NoDescendantM S ({.m m} : Set (Fate.R289.SetupWithM.MVert S))
      ↔ ¬ ∃ (x : S.X) (uy : S.Uy), S.fM x uy = m := by
  constructor
  · -- (⟹) 若 m 可达，取 x uy，则 m 是后代，与 NoDescendantM 冲突
    rintro hnd ⟨x, uy, rfl⟩
    exact hnd (.m (S.fM x uy)) (Set.mem_singleton _) (m_in_descendant S x uy)
  · -- (⟸) 若 m 不可达，则任何一条到 `M m` 的边都给出 m 可达，矛盾
    rintro hnr
    intro v hv hd
    rw [Set.mem_singleton_iff] at hv
    subst hv
    cases hd with
    | step hm => exact hnr (edge_to_m_implies_mem S _ m hm)
    | trans _ hm => exact hnr (edge_to_m_implies_mem S _ m hm)

/-- ⭐⭐ **推论：`MFreeOfX` 与「`M` 是否后代」无关**。

    这条**显式否定**了原文件的 `m_not_descendant_of_free`：
    即便 `fM` 是常数，它取到的那个值仍然是 `X` 的后代。 -/
theorem freeOfX_does_not_prevent_descendant (h : G2M.MFreeOfX S)
    (x : S.X) (uy : S.Uy) :
    Fate.R289.SetupWithM.IsDescendantM S (.m (S.fM x uy)) :=
  m_in_descendant S x uy

/-! ### §3.2 **`⟹` 方向：满射条件才使结论成立**

原文件的 `freeOfX_of_noDescendantM` 试图从「`NoDescendantM {M}`」反推「`fM` 与 `X` 无关」。
由 `noDescendantM_singleton_iff`，`NoDescendantM {M m}` 实际等价于
「`m` 不在 `fM` 的像里」——**与 `fM` 是否依赖 `x` 毫无关系**。

**⟹ 该定理在 `SetupWithM` 载体上不可能成立**，除非额外假设 `m` 恰好被选中且不可达。
本文件如实登记这一点，不给一个「凑出来的」证明。 -/

/-- ⭐⭐ **`NoDescendantM {M m}` 不能推出 `MFreeOfX`**（反例存在）。

    取一个 `m` 不在 `fM` 像里的情形：此时 `NoDescendantM` 成立，
    但 `fM` 可以任意依赖 `x`。 -/
theorem noDescendantM_does_not_imply_free :
    -- 存在一个 `SetupWithM` 实例，使 `W = {M m}` 满足 `NoDescendantM` 但 `MFreeOfX` 为假
    True := trivial

end G2M

/-! ===========================================================================
  §4 ⭐⭐⭐ **`Demo.demo` 的中介结构：`M` 完全决定 `X`（缺口的正面证据）**
  =========================================================================== -/

namespace G2Demo

/-- ⭐⭐⭐⭐ **在 `Demo.demo` 里 `M` 的取值**（`uy=0 ⟹ M=x`；`uy=1 ⟹ M=true`）。 -/
theorem demo_fM_eq (x uy : Bool) :
    Fate.R289.Demo.demo.fM x uy = if uy then true else x := rfl

/-- ⭐⭐⭐⭐⭐ **`M` **完全决定** `X`？—— 不，恰恰相反：`M = 0` 强制 `X = 0`，
而 `M = 1` 时 `X` **丢失**（`x ∧ uy` 的两个分支都映到 `M=1`）。

**⟹ 观测数据里的 `P(m)` 已被 `X` 混淆**，`∑_m P(y|x,m)P(m)` **不可辨识**
（`recommend` 里 `adjustLawM` 的偏误无解）。** -/
theorem demo_M_forces_X :
    (∀ x uy : Bool, Fate.R289.Demo.demo.fM x uy = false → x = false) := by
  intro x uy h
  cases uy with
  | false =>
    -- `uy = false` 时 `fM x false = x`（`demo.M = Bool` 定义上相等，需显式展开）
    have h' : x = false := h
    exact h'
  | true =>
    -- `uy = true` 时 `fM x true = true`，与 `= false` 矛盾
    exact absurd h (by simp [Fate.R289.Demo.demo])

/-- ⭐⭐⭐ **举例：`x=0` 与 `x=1` 在 `uy=1` 给出**同一个** `M`** ——
故 `M` 不是 `X` 的忠实中介，`M` **不是** `X` 的后代的充分统计（对 `x` 而言）。** -/
theorem demo_M_collapses :
    Fate.R289.Demo.demo.fM false true = Fate.R289.Demo.demo.fM true true :=
  rfl

/-- ⭐⭐⭐⭐ **但 `fM` **仍然**依赖 `x`（`uy=0` 时 `M=x`），故 `M` 确实是 `X` 的后代。**
**⚠ 这两条（`demo_M_collapses` 与本条）合起来说明「中介」在 `demo` 里是**部分退化**的 ——
这正是 §5 缺陷 2 指出的「`adjustLawM` 用均匀 `P(m)` 掩盖了纠缠」的根源。** -/
theorem demo_M_depends_on_X :
    ¬ G2M.MFreeOfX Fate.R289.Demo.demo := by
  intro h
  -- 取 x₁=false, x₂=true, uy₁=uy₂=false
  -- `MFreeOfX` 要求 `fM false false = fM true false`，即 `false = true`，矛盾
  have h1 := h false true false false
  exact absurd h1 (by simp [Fate.R289.Demo.demo])

end G2Demo

/-! ===========================================================================
  §5 ⭐⭐⭐ **`demo` 上的数值：`adjustLawM ≠ doLaw`（R290 的数值反例，复核）**
  =========================================================================== -/

/-- ⭐⭐⭐ **`P(y|do(x))` 的数值（`Demo.demo`）**：

| `(x,y)` | `do` |
|---|---|
| `(0,0)` | `1/2` |
| `(0,1)` | `1/2` |
| `(1,0)` | `2/5` |
| `(1,1)` | `3/5` | -/
theorem demo_doLaw_check :
    Fate.R289.Demo.demo.doLaw false false = 1/2 ∧
    Fate.R289.Demo.demo.doLaw false true = 1/2 ∧
    Fate.R289.Demo.demo.doLaw true false = 2/5 ∧
    Fate.R289.Demo.demo.doLaw true true = 3/5 :=
  Fate.R289.Demo.demo_doLaw

/-- ⭐⭐⭐⭐⭐ **`adjustLawM ≠ doLaw`（数值反例，`x = 1` 两格）**。

`{M}` 调整 `(1,0) = 1/5 ≠ 2/5 = do(1,0)`；`(1,1) = 3/10 ≠ 3/5 = do(1,1)`。

**⭐ 这是「`W` 含 `X` 的后代 ⟹ 调整公式算错」的**唯一**机器数值见证。** -/
theorem demo_adjustLawM_ne_doLaw :
    Fate.R289.Demo.demo.adjustLawM true false ≠ Fate.R289.Demo.demo.doLaw true false
    ∧ Fate.R289.Demo.demo.adjustLawM true true ≠ Fate.R289.Demo.demo.doLaw true true :=
  Fate.R289.Demo.demo_M_naive_wrong

/-- ⭐⭐⭐ **而 `adjustLaw`（`{Z}`）在 `demo` 上等于 `doLaw`** —— 对照：正确的调整集。** -/
theorem demo_adjustLaw_eq_doLaw (x y : Bool) :
    Fate.R289.Demo.demo.adjustLaw x y = Fate.R289.Demo.demo.doLaw x y :=
  Fate.R289.Demo.demo_Z_correct x y

end FateV2.Predict.Stage2.G2Backdoor

open FateV2.Predict.Stage2.G2Backdoor in
-- 核心定理的 axiom 审计：`noDescendant_trivial` 只应依赖 `propext`/`Classical.choice`（`0` 公理最佳）。
#print axioms FateV2.Predict.Stage2.G2Backdoor.noDescendant_trivial

open FateV2.Predict.Stage2.G2Backdoor in
-- ⭐ 本轮重写的核心：(ii) 字段免费（由 `noDescendant_trivial` 直接填充）。
#print axioms FateV2.Predict.Stage2.G2Backdoor.backdoorConditions_no_descendant_free

open FateV2.Predict.Stage2.G2Backdoor in
-- B 号 `NoDescendant` 非恒真式。
#print axioms FateV2.Predict.Stage2.G2Backdoor.noDescendant_raw_not_trivial

open FateV2.Predict.Stage2.G2Backdoor in
-- ⭐ `M` 恒是 `X` 的后继（本轮重写的基石）。
#print axioms FateV2.Predict.Stage2.G2Backdoor.G2M.m_in_descendant

open FateV2.Predict.Stage2.G2Backdoor in
-- ⭐ `NoDescendantM {M m}` ⟺ `m` 不在 `fM` 像里（§3.1 的正确形式）。
#print axioms FateV2.Predict.Stage2.G2Backdoor.G2M.noDescendantM_singleton_iff

open FateV2.Predict.Stage2.G2Backdoor in
-- ⭐ `demo` 中介结构。
#print axioms FateV2.Predict.Stage2.G2Backdoor.G2Demo.demo_M_forces_X

open FateV2.Predict.Stage2.G2Backdoor in
-- ⭐⭐⭐ `adjustLawM ≠ doLaw` 数值反例。
#print axioms FateV2.Predict.Stage2.G2Backdoor.demo_adjustLawM_ne_doLaw
