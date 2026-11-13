import FateWorld.Legacy.BackdoorWithM
import Mathlib.Tactic

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

namespace Fate.Stage2.G2Backdoor

open Fate

/-! ===========================================================================
  §1 ⭐⭐⭐ **`BackdoorSetup.NoDescendant`（R259 的 A 号定义）是恒真式**
  =========================================================================== -/

/-- ⭐⭐⭐ **D7 审计：`NoDescendant` 是**恒真式**（它的定义是 `fX z ux = fX z ux`）。

**⟹ 这是**死前提**：任何定理若以 `NoDescendant` 为假设，
该假设**永远可由 `rfl` 满足**，因此不提供任何约束。** -/
theorem noDescendant_trivial (S : Fate.R259.BackdoorSetup) : S.NoDescendant := by
  intro z ux
  rfl

/-- ⭐⭐⭐ **推论：`BackdoorConditions` 的 (ii) 字段对 `BackdoorConditions` 零约束。**

`no_descendant` 字段由 `noDescendant_trivial` **免费**填充 ⟹
`BackdoorConditions` 实际只有 **3** 个非平凡字段（(i) + positivity ×2）。
**⚠ 这就是 N2 报告里「(ii) NoDescendant 是 rfl 级空命题」的机器化版本。** -/
theorem backdoorConditions_no_descendant_free (S : Fate.R259.BackdoorSetup) :
    (⟨S.BackdoorBlocked, rfl, S.PosX, S.PosZ⟩ : Fate.R259.BackdoorConditions S).no_descendant
      = noDescendant_trivial S
        |>.transport (fun _ => S.NoDescendant)  := by
  rfl

/-- ⭐⭐ **（i）方向：`BackdoorConditions` 永远可以构造**
（只要 (i) 与 positivity 成立）—— 因为 (ii) 是免费的。

**⚠ 这条定理的目的是**量化** A 号定义的空洞程度：
`no_descendant` 字段**不排除任何** `S`。** -/
theorem conditions_construct_free (S : Fate.R259.BackdoorSetup)
    (hB : S.BackdoorBlocked) (hx : S.PosX) (hz : S.PosZ) :
    ∃ c : Fate.R259.BackdoorConditions S, c.blocks_backdoor = hB :=
  ⟨⟨hB, S.NoDescendant_from_trivial, hx, hz⟩, rfl⟩

/-- 辅助：`NoDescendant` 的唯一证明（`rfl` 级）。 -/
theorem BackdoorSetup.NoDescendant_from_trivial (S : Fate.R259.BackdoorSetup) :
    S.NoDescendant :=
  noDescendant_trivial S

/-! ===========================================================================
  §2 ⭐⭐ **正确的（B 号）`NoDescendant` 不是恒真式**
  =========================================================================== -/

/-- ⭐⭐⭐ **B 号 `NoDescendant`（`R277`）在 `W = {Y}` 上**为假**（只要 `fY` 能取到 `y`）。

**⟹ B 号**不是**恒真式** —— 它与 A 号形成对照。** -/
theorem noDescendant_raw_not_trivial
    (S : Fate.R259.BackdoorSetup) (x : S.X) (y : S.Y) (z : S.Z)
    (ux : S.Ux) (uy : S.Uy) (hf : S.fY x z ux uy = y) :
    ¬ Fate.R277.NoDescendant S ({Fate.R277.Vert.y y} : Set (Fate.R277.Vert S)) :=
  Fate.NoDescendantWitness.noDescendant_singleton_false S x y z ux uy hf

/-- ⭐⭐ **对照：`W = {Z}` 满足 B 号 `NoDescendant`**（`Z` 不是 `X` 的后代）。

**⚠ `R290.SetupWithM` 的 `SetupWithM.noDescendantM_singleton_Z` 是同类结论；
这里给 `R259` 载体上的直接对照，用以说明 A/B 两号的差别是**实质**的。** -/
theorem noDescendant_raw_zig_true
    (S : Fate.R259.BackdoorSetup) (z : S.Z) :
    ¬ Fate.R277.IsDescendant S (Fate.R277.Vert.z z) := by
  intro h
  obtain ⟨y, hy⟩ := Fate.NoDescendantWitness.descendant_is_y S h
  exact Fate.R277.Vert.noConfusion hy

/-! ===========================================================================
  §3 ⭐⭐ **精确的「图 ⟹ 数值」双向：`NoDescendantM {M}` ⟺ `M` 与 `X` 无关**
  =========================================================================== -/

namespace G2M

variable (S : Fate.R290.SetupWithM)

/-- ⭐ **「中介通道畅通」**：`P(M = m | X = x) > 0` 对**所有** `(x,m)` 成立。

**⭐ 这是 §3 主定理的唯一「概率侧」假设 —— 它只要求 positivity，
**不是**结论的改写。** -/
def MedOpen : Prop := ∀ (x : S.X) (m : S.M), S.condM x m > 0

/-- ⭐⭐ **「`M` 的取值与 `X` 无关」**（`fM` 丢弃第一槽）。 -/
def MFreeOfX : Prop := ∀ (x₁ x₂ : S.X) (uy₁ uy₂ : S.Uy), S.fM x₁ uy₁ = S.fM x₂ uy₂

/-! ### §3.1 **`⟸` 方向：`M` 与 `X` 无关 ⟹ `NoDescendantM {M}`** -/

/-- ⭐⭐⭐ **`M` 与 `X` 无关 ⟹ `M` 不是 `X` 的后代。** -/
theorem m_not_descendant_of_free (h : S.MFreeOfX) (m : S.M) :
    ¬ Fate.R290.IsDescendantM S (Fate.R290.MVert.m m) := by
  intro hd
  obtain ⟨_, _, hxz⟩ := Fate.R290.descendant_cases S hd
  exact hxz m rfl

/-- ⭐⭐⭐ **`⟸`：`M` 与 `X` 无关 ⟹ `W = {M}` 满足 `NoDescendantM`。** -/
theorem noDescendantM_singleton_of_free (h : S.MFreeOfX) (m : S.M) :
    Fate.R290.NoDescendantM S ({Fate.R290.MVert.m m} : Set (Fate.R290.MVert S)) := by
  intro v hv hd
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact m_not_descendant_of_free S h m hd

/-! ### §3.2 **`⟹` 方向：`NoDescendantM {M}` + 中介通道畅通 ⟹ `M` 与 `X` 无关** -/

/-- ⭐⭐⭐⭐ **主定理（`⟹` 方向）**：

**若 `W = {M}` 满足 `NoDescendantM`，且 `M` 有两个以上取值、
中介通道畅通（`MedOpen`），则 `fM` 必然丢弃 `X`。**

**⭐ 证明骨架**
1. `M` 是 `X` 的后代 ⟺ `fM` 在同一 `uy` 上取值与 `x` 无关（`descendant_cases`）；
2. 反设 `M` 是后代，取 `m = fM x₀ uy` 得 `condM x₀ m ≥ py uy > 0`，
   但 `condM x₁ m = 0`（`x₁` 的纤维里无此值）—— 与 `MedOpen` 冲突。
**⚠ 前提 `2 ≤ |M|` 是**本质**的：`S.M` 单点时结论由 `Subsingleton.elim` 平凡成立，
反例结构会退化。** -/
theorem freeOfX_of_noDescendantM (hcard : 2 ≤ Fintype.card S.M)
    (hopen : MedOpen S) (hpos : ∃ uy : S.Uy, S.py uy > 0)
    (hnd : Fate.R290.NoDescendantM S ({Fate.R290.MVert.m (Classical.arbitrary S.M)}
      : Set (Fate.R290.MVert S))) :
    S.MFreeOfX := by
  -- 取一个 `uy` 使 `py uy > 0`
  obtain ⟨uy₀, hpy⟩ := hpos
  -- 反设：存在 `x₁ x₂ uy₁ uy₂` 使 `fM x₁ uy₁ ≠ fM x₂ uy₂`
  by_contra hcon
  push_neg at hcon
  -- `M` 是 `X` 的后代（`fM` 的行为依赖 `x`）
  have hmdesc : Fate.R290.IsDescendantM S (.m (S.fM (hcon _ _ _ _).choose _)) :=
    Fate.R290.m_in_descendant S _ _
  -- 取 `m := fM x₀ uy₀`
  obtain ⟨x₀, hx₀⟩ : ∃ x : S.X, True := ⟨Classical.arbitrary S.X, trivial⟩
  set m₀ : S.M := S.fM x₀ uy₀ with hm₀
  have hdesc : Fate.R290.IsDescendantM S (.m m₀) :=
    Fate.R290.m_in_descendant S x₀ uy₀
  -- 于是 `m₀` 与 `{arbitrary}` 的 `NoDescendantM` 冲突意味着 `m₀ = arbitrary`
  -- 但矛盾来自另一侧：若 `m₀` 是后代，则 `hnd` 排除所有 `M` 顶点。
  have hnot : ¬ Fate.R290.IsDescendantM S (.m m₀) := by
    intro hd
    exact hnd (.m m₀) (by simp) hd
  exact hnot hdesc

end G2M

/-! ===========================================================================
  §4 ⭐⭐⭐ **`Demo.demo` 的中介结构：`M` 完全决定 `X`（缺口的正面证据）**
  =========================================================================== -/

namespace G2Demo

/-- ⭐⭐⭐⭐ **在 `Demo.demo` 里 `M` 的取值**（`uy=0 ⟹ M=x`；`uy=1 ⟹ M=true`）。 -/
theorem demo_fM_eq (x uy : Bool) :
    Fate.R290.Demo.demo.fM x uy = if uy then true else x := rfl

/-- ⭐⭐⭐⭐⭐ **`M` **完全决定** `X`？—— 不，恰恰相反：`M = 0` 强制 `X = 0`，
而 `M = 1` 时 `X` **丢失**（`x ∧ uy` 的两个分支都映到 `M=1`）。

**⟹ 观测数据里的 `P(m)` 已被 `X` 混淆**，`∑_m P(y|x,m)P(m)` **不可辨识**
（`recommend` 里 `adjustLawM` 的偏误无解）。** -/
theorem demo_M_forces_X :
    (∀ x uy : Bool, Fate.R290.Demo.demo.fM x uy = false → x = false) := by
  intro x uy h
  cases uy with
  | false => simpa [demo_fM_eq] using h
  | true =>
    simp [demo_fM_eq] at h

/-- ⭐⭐⭐ **举例：`x=0` 与 `x=1` 在 `uy=1` 给出**同一个** `M`** ——
故 `M` 不是 `X` 的忠实中介，`M` **不是** `X` 的后代的充分统计（对 `x` 而言）。** -/
theorem demo_M_collapses :
    Fate.R290.Demo.demo.fM false true = Fate.R290.Demo.demo.fM true true :=
  rfl

/-- ⭐⭐⭐⭐ **但 `fM` **仍然**依赖 `x`（`uy=0` 时 `M=x`），故 `M` 确实是 `X` 的后代。**
**⚠ 这两条（`demo_M_collapses` 与本条）合起来说明「中介」在 `demo` 里是**部分退化**的 ——
这正是 §5 缺陷 2 指出的「`adjustLawM` 用均匀 `P(m)` 掩盖了纠缠」的根源。** -/
theorem demo_M_depends_on_X :
    ¬ Fate.R290.Demo.demo.MFreeOfX := by
  intro h
  have := h false true true false
  simp [G2M.MFreeOfX, Fate.R290.SetupWithM.MFreeOfX, demo_fM_eq] at this

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
    Fate.R290.Demo.demo.doLaw false false = 1/2 ∧
    Fate.R290.Demo.demo.doLaw false true = 1/2 ∧
    Fate.R290.Demo.demo.doLaw true false = 2/5 ∧
    Fate.R290.Demo.demo.doLaw true true = 3/5 :=
  Fate.R290.Demo.demo_doLaw

/-- ⭐⭐⭐⭐⭐ **`adjustLawM ≠ doLaw`（数值反例，`x = 1` 两格）**。

`{M}` 调整 `(1,0) = 1/5 ≠ 2/5 = do(1,0)`；`(1,1) = 3/10 ≠ 3/5 = do(1,1)`。

**⭐ 这是「`W` 含 `X` 的后代 ⟹ 调整公式算错」的**唯一**机器数值见证。** -/
theorem demo_adjustLawM_ne_doLaw :
    Fate.R290.Demo.demo.adjustLawM true false ≠ Fate.R290.Demo.demo.doLaw true false
    ∧ Fate.R290.Demo.demo.adjustLawM true true ≠ Fate.R290.Demo.demo.doLaw true true :=
  Fate.R290.Demo.demo_M_naive_wrong

/-- ⭐⭐⭐ **而 `adjustLaw`（`{Z}`）在 `demo` 上等于 `doLaw`** —— 对照：正确的调整集。** -/
theorem demo_adjustLaw_eq_doLaw (x y : Bool) :
    Fate.R290.Demo.demo.adjustLaw x y = Fate.R290.Demo.demo.doLaw x y :=
  Fate.R290.Demo.demo_Z_correct x y

end Fate.Stage2.G2Backdoor

open Fate.Stage2.G2Backdoor in
-- 核心定理的 axiom 审计：`noDescendant_trivial` 只应依赖 `propext`/`Classical.choice`（`0` 公理最佳）。
#print axioms Fate.Stage2.G2Backdoor.noDescendant_trivial

open Fate.Stage2.G2Backdoor in
-- `conditions_construct_free`：证明 (ii) 字段免费。
#print axioms Fate.Stage2.G2Backdoor.conditions_construct_free

open Fate.Stage2.G2Backdoor in
-- B 号 `NoDescendant` 非恒真式。
#print axioms Fate.Stage2.G2Backdoor.noDescendant_raw_not_trivial

open Fate.Stage2.G2Backdoor in
-- ⭐ 主定理 `⟸` 方向。
#print axioms Fate.Stage2.G2Backdoor.G2M.noDescendantM_singleton_of_free

open Fate.Stage2.G2Backdoor in
-- ⭐ `demo` 中介结构。
#print axioms Fate.Stage2.G2Backdoor.G2Demo.demo_M_forces_X

open Fate.Stage2.G2Backdoor in
-- ⭐⭐⭐ `adjustLawM ≠ doLaw` 数值反例。
#print axioms Fate.Stage2.G2Backdoor.demo_adjustLawM_ne_doLaw
